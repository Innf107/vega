#include "preprocessing.h"
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/ErrorHandling.h>
#include <llvm/Support/raw_ostream.h>

unsigned numberOfReturnedBoxedPointers(Type* type) {
    if (type->isPointerTy() && type->getPointerAddressSpace() == 1) {
        return 1;
    }
    if (type->isStructTy()) {
        // we assume that all pointers are stored first in sret allocas
        return numberOfReturnedBoxedPointers(type->getStructElementType(0));
    }
    if (type->isArrayTy()) {
        if (!type->getArrayElementType()->isPointerTy() ||
            type->getArrayElementType()->getPointerAddressSpace() != 1) {
            return 0;
        }
        return (unsigned)type->getArrayNumElements();
    }
    return 0;
}

std::string renderInstruction(Value* instruction) {
    std::string instruction_string;
    llvm::raw_string_ostream instruction_stream(instruction_string);
    instruction_stream << *instruction;
    return instruction_string;
}

void replaceReadsFromPointer(unsigned byteOffsetFromBase,
    Function& function,
    Value* pointerToReplace,
    IRBuilder<>& readBuilder,
    Value* sretPointer,
    SmallVector<std::optional<Value*>>& cachedDirectReads) {
    for (auto& use : pointerToReplace->uses()) {
        auto* instruction = use.getUser();
        if (isa<CallBase>(instruction)) {
            outs() << "pointer: " << *pointerToReplace << " |    instr: " << *instruction << "\n";
            // tiny sanity check that this is probably (hopefully) only the
            // original sret that wrote to this
            assert(dyn_cast<CallBase>(instruction)->hasStructRetAttr());
            continue;
        } else if (isa<GetElementPtrInst>(instruction)) {
            auto* gepInstruction = dyn_cast<GetElementPtrInst>(instruction);

            auto byteOffset = APInt::getZero(64);
            auto isConstantOffset = gepInstruction->accumulateConstantOffset(
                function.getDataLayout(), byteOffset);
            if (!isConstantOffset) {
                llvm::reportFatalUsageError(
                    Twine("sret (or sret-derived) pointer '" +
                        Twine(pointerToReplace->getName()) +
                        "' used in non-constant GEP instruction: " +
                        renderInstruction(instruction)));
                return;
            }
            replaceReadsFromPointer(
                byteOffsetFromBase + byteOffset.getZExtValue(),
                function,
                gepInstruction,
                readBuilder,
                sretPointer,
                cachedDirectReads);
        } else if (isa<LoadInst>(instruction)) {
            auto* readAsType = instruction->getType();
            if (readAsType->isPointerTy()) {
                assert(readAsType->getPointerAddressSpace() == 1);
                assert((byteOffsetFromBase & 0b111) == 0);

                auto* pointer = (byteOffsetFromBase != 0)
                    ? readBuilder.CreateInBoundsPtrAdd(
                          sretPointer, readBuilder.getInt64(byteOffsetFromBase))
                    : sretPointer;
                auto earlyLoad = readBuilder.CreateLoad(
                    readAsType, pointer, instruction->getName());
                instruction->replaceAllUsesWith(earlyLoad);
            } else if (readAsType->isVectorTy()) {
                assert(dyn_cast<VectorType>(readAsType)
                           ->getElementType()
                           ->isPointerTy() &&
                    readAsType->getPointerAddressSpace() == 1);

                auto* pointer = (byteOffsetFromBase != 0)
                    ? readBuilder.CreateInBoundsPtrAdd(
                          sretPointer, readBuilder.getInt64(byteOffsetFromBase))
                    : sretPointer;
                auto earlyLoad = readBuilder.CreateLoad(
                    readAsType, pointer, instruction->getName());
                instruction->replaceAllUsesWith(earlyLoad);
            } else {
                llvm::reportFatalUsageError(
                    Twine("sret (or sret-derived) pointer '" +
                        Twine(pointerToReplace->getName()) +
                        "' loaded from as non-pointer or pointer vector in "
                        "instruction: " +
                        renderInstruction(instruction)));
                return;
            }
        } else {
            llvm::reportFatalUsageError(
                Twine("sret (or sret-derived) pointer '" +
                    Twine(pointerToReplace->getName()) +
                    "' used in non-replacable instruction: " +
                    renderInstruction(instruction)));
            return;
        }
    }
}

// Our shadow stack pass only tracks boxed *variables*.
// It doesn't track boxed pointers stored in allocas, which isn't
// possible in general anyway since LLVM's memory is untyped, so
// it is very important that layout generation normally never stores boxed
// pointers in allocas.
// However, there is one case where we *have* to allocate
// allocas containing boxed pointers: sret pointers.
// If LLVM's optimizations move a read from an sret pointer past a safepoint,
// we will not track it in the shadow stack.
//
// To combat this problem, this pass adds reads after every call with an alloca
// variable containing boxed pointers and replaces all further reads from the
// alloca with that early read.
//
// This is only sound because every call gets its own sret alloca and this
// alloca is only written to by that call.
void fixSRetAllocas(Function& function) {
    IRBuilder builder(function.getContext());
    for (auto& block : function) {
        for (auto& instruction : block) {
            auto* callInstruction = dyn_cast<CallBase>(&instruction);
            if (callInstruction == nullptr ||
                !callInstruction->hasStructRetAttr()) {
                continue;
            }
            auto* sretArgument = callInstruction->getArgOperand(0);
            auto* sretAlloca = dyn_cast<AllocaInst>(sretArgument);
            if (sretAlloca == nullptr) {
                continue;
            }
            unsigned numberOfPointers =
                numberOfReturnedBoxedPointers(sretAlloca->getAllocatedType());
            if (numberOfPointers == 0) {
                continue;
            }

            SmallVector<std::optional<Value*>> cachedDirectReads(
                numberOfPointers);
            SmallDenseMap<std::pair<Value*, unsigned>, Value*>
                cachedVectorReads;

            // SAFETY: calls are not terminators so getNextNode always exists
            builder.SetInsertPoint(callInstruction->getNextNode());

            replaceReadsFromPointer(0,
                function,
                sretAlloca,
                builder,
                sretAlloca,
                cachedDirectReads);
        }
    }
}
