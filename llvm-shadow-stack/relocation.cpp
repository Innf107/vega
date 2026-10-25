#include "relocation.h"
#include "frame_allocation.h"
#include "pointer_ids.h"
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

using namespace llvm;

void saveToShadowStackIfNecessary(IRBuilder<>& builder,
    std::optional<Instruction*> instruction,
    PointerIDs pointerIDs,
    BitSet liveAcrossCalls,
    StackFrameAssignments stackFrameAssignments,
    Value* stackFramePointers,
    Value* value) {
    if (isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls, value)) {
        // SAFETY: terminators don't return anything so it's okay to use
        // getNextNode here
        if (instruction.has_value()) {
            auto* nextNonPhiInstruction = instruction.value()->getNextNode();
            while (isa<PHINode>(nextNonPhiInstruction)) {
                nextNonPhiInstruction = nextNonPhiInstruction->getNextNode();
            }
            builder.SetInsertPoint(nextNonPhiInstruction);
        }
        assert(stackFrameAssignments.assignments.contains(value));
        unsigned slot = stackFrameAssignments.assignments.lookup(value);
        auto* stackSlotPointer =
            builder.CreateGEP(PointerType::get(value->getContext(), 1),
                stackFramePointers,
                {builder.getInt64(slot)},
                "stack-slot");
        builder.CreateStore(value, stackSlotPointer);
    }
}

SmallDenseMap<Value*, Value*> intersectionOfPredecessorRelocations(
    BasicBlock* block,
    SmallDenseMap<BasicBlock*, SmallDenseMap<Value*, Value*>>&
        relocatedOutOfBlocks) {
    if (block->hasNPredecessors(0)) {
        return SmallDenseMap<Value*, Value*>();
    }
    if (auto* predecessor = block->getSinglePredecessor()) {
        return relocatedOutOfBlocks[predecessor];
    }

    SmallVector<SmallDenseMap<Value*, Value*>> predecessors;
    for (auto* predecessorBlock : llvm::predecessors(block)) {
        predecessors.push_back(relocatedOutOfBlocks[predecessorBlock]);
    }
    SmallDenseMap<Value*, Value*> intersection;

    for (auto& [k, v] : predecessors[0]) {
        bool is_in_intersection = true;
        for (int i = 1; i < predecessors.size(); i++) {
            if (!predecessors[i].contains(k) || predecessors[i][k] != v) {
                is_in_intersection = false;
                break;
            }
        }
        if (is_in_intersection) {
            intersection[k] = v;
        }
    }
    return intersection;
}
Value* relocate(IRBuilder<>& builder,
    Value* valueToRelocate,
    StackFrameAssignments& stackFrameAssignments,
    Value* stackFramePointers) {
    assert(stackFrameAssignments.assignments.contains(valueToRelocate));
    unsigned slot = stackFrameAssignments.assignments.lookup(valueToRelocate);

    auto* gcPointerType = PointerType::get(valueToRelocate->getContext(), 1);
    auto* stackSlotPointer = builder.CreateGEP(gcPointerType,
        stackFramePointers,
        {builder.getInt64(slot)},
        "stack-slot");

    return builder.CreateLoad(gcPointerType,
        stackSlotPointer,
        valueToRelocate->getName() + ".relocated");
}

bool isTailCallInstruction(Instruction* instruction) {
    if (instruction == nullptr) {
        return false;
    }
    auto* callInstruction = dyn_cast<CallBase>(instruction);
    return callInstruction->isTailCall();
}

void popStackOnExits(
    Function& function, Value* threadStatePointer, Value* shadowStackFrame) {
    for (auto& block : function) {
        if (isa<ReturnInst>(block.getTerminator())) {
            auto* lastNonReturnInstruction =
                block.getTerminator()->getPrevNode();

            IRBuilder builder(function.getContext());
            // We don't need to check if the tail call here is a *literal* tail
            // call. Even if it keeps its stack frame, every pointer in it is
            // still dead after the return so we can still pop its shadow stack
            // frame.
            // (If it is a real tail call, we *need* to pop its shadow stack
            // frame however)
            if (lastNonReturnInstruction != nullptr &&
                isa<CallBase>(lastNonReturnInstruction)) {
                builder.SetInsertPoint(lastNonReturnInstruction);
            } else {
                builder.SetInsertPoint(block.getTerminator());
            }

            auto* previousFrame = builder.CreateLoad(
                PointerType::get(function.getContext(), 0), shadowStackFrame);
            builder.CreateStore(previousFrame, threadStatePointer);
        }
    }
}

// TODO: we need to clear out stack slots once
// they're dead
void saveAndRelocateBoxedPointers(Function& function,
    PointerIDs pointerIDs,
    BitSet liveAcrossCalls,
    StackFrameAssignments stackFrameAssignments) {
    if (stackFrameAssignments.frameSize == 0) {
        return;
    }

    auto& context = function.getContext();

    const auto threadStatePointer =
        function.hasParamAttribute(0, Attribute::AttrKind::StructRet)
        ? function.getArg(1)
        : function.getArg(0);

    IRBuilder builder(context);

    builder.SetInsertPointPastAllocas(&function);

    auto* frameStructType = StructType::get(context,
        {// Pointer to the previous segment. This has to be in address
         // space 0, not 1 since it's not heap allocated itself
            PointerType::get(context, 0),
            // Size (doesn't need to be 64 bit but we can't make it less
            // because of alignment so it doesn't matter)
            Type::getInt64Ty(context),
            // The actual pointers. These have to be in address space 1.
            ArrayType::get(PointerType::get(context, 1),
                stackFrameAssignments.frameSize)});
    auto* shadowStackStruct =
        builder.CreateAlloca(frameStructType, nullptr, "shadow-stack-frame");

    // The thread state contains the shadow stack at offset 0
    auto* previousShadowStackPointer =
        builder.CreateLoad(PointerType::get(context, 0),
            threadStatePointer,
            "previous-shadow-stack-frame");

    // the previous pointer is stored at offset 0 in the shadow stack frame
    builder.CreateStore(previousShadowStackPointer, shadowStackStruct);

    builder.CreateStore(shadowStackStruct, threadStatePointer);

    auto* pointerToSize = builder.CreateInBoundsGEP(frameStructType,
        shadowStackStruct,
        {builder.getInt32(0), builder.getInt32(1)},
        "size-slot");
    builder.CreateStore(
        builder.getInt64(stackFrameAssignments.frameSize), pointerToSize);

    auto* stackFramePointers = builder.CreateInBoundsGEP(frameStructType,
        shadowStackStruct,
        {builder.getInt32(0), builder.getInt32(2)},
        "shadow-stack-pointers");
    builder.CreateMemSetInline(stackFramePointers,
        MaybeAlign(8),
        builder.getInt8(0),
        builder.getInt64(8 * stackFrameAssignments.frameSize));

    popStackOnExits(function, threadStatePointer, shadowStackStruct);

    for (Argument& argument : function.args()) {
        saveToShadowStackIfNecessary(builder,
            std::nullopt,
            pointerIDs,
            liveAcrossCalls,
            stackFrameAssignments,
            stackFramePointers,
            &argument);
    }

    for (auto& block : function) {
        for (auto& instruction : block) {
            saveToShadowStackIfNecessary(builder,
                std::make_optional(&instruction),
                pointerIDs,
                liveAcrossCalls,
                stackFrameAssignments,
                stackFramePointers,
                &instruction);
        }
    }

    SmallDenseMap<BasicBlock*, SmallDenseMap<Value*, Value*>>
        relocatedOutOfBlocks;

    for (auto* block : depth_first(&function)) {
        SmallDenseMap<Value*, Value*> alreadyRelocated =
            intersectionOfPredecessorRelocations(block, relocatedOutOfBlocks);
        if (block->isEntryBlock()) {
            for (auto& parameter : function.args()) {
                if (isGCPointerLiveAcrossCall(
                        pointerIDs, liveAcrossCalls, &parameter)) {
                    alreadyRelocated[&parameter] = &parameter;
                }
            }
        }

        for (auto& instruction : *block) {

            // We handle phi arguments at the end of their parent block.
            // Everything else here still applies to them though.
            if (!isa<PHINode>(instruction)) {
                // relocate the operands
                for (auto& operandUse : instruction.operands()) {
                    auto* operand = operandUse.get();
                    if (!isGCPointerLiveAcrossCall(
                            pointerIDs, liveAcrossCalls, operand)) {
                        continue;
                    }

                    auto* cached_relocation = alreadyRelocated.lookup(operand);
                    if (cached_relocation != nullptr) {
                        operandUse.set(cached_relocation);
                    } else {

                        builder.SetInsertPoint(&instruction);
                        auto* relocation = relocate(builder,
                            operand,
                            stackFrameAssignments,
                            stackFramePointers);
                        alreadyRelocated[operand] = relocation;
                        operandUse.set(relocation);
                    }
                }
            }

            if (isVegaGCCall(instruction)) {
                // After a gc call, we need to relocate everything again
                alreadyRelocated.clear();
            }

            // The result of an instruction doesn't need to be relocated until
            // we hit a gc call, so we can treat it as if it had already been
            // relocated.
            // It is important that this happens *after* we clear the
            // relocations, since the result of a call does not need to be
            // invalidated
            if (isGCPointerLiveAcrossCall(
                    pointerIDs, liveAcrossCalls, &instruction)) {
                alreadyRelocated[&instruction] = &instruction;
            }

            // Tail calls need to be modified to use the previous shadow stack
            // pointer, since our stack frame isn't even alive after the tail
            // call
            if (isa<CallInst>(instruction)) {
                auto* call = dyn_cast<CallInst>(&instruction);
                // Just having a tail specifier is not enough here. LLVM
                // optimizations can create tail annotations on calls that are
                // not actually in tail position.
                //
                // In these cases, we do need to pass the modified stack frame.
                if (call->isTailCall()) {
                    if (isa<ReturnInst>(call->getNextNode())) {
                        for (auto& operandUse : call->operands()) {
                            if (operandUse == shadowStackStruct) {
                                operandUse.set(previousShadowStackPointer);
                            }
                        }
                    } else {
                        // This probably isn't strictly necessary as long as we
                        // run the shadow stack pass last, but if we ever want
                        // to run any other optimizations after it, we need to
                        // make sure that these calls aren't treated as tail
                        // calls (since they're not tail-call safe anymore)
                        call->setTailCall(false);
                    }
                }
            }
        }

        for (auto* successor : successors(block)) {
            for (auto& phi : successor->phis()) {
                auto* incoming = phi.getIncomingValueForBlock(block);
                if (!isGCPointerLiveAcrossCall(
                        pointerIDs, liveAcrossCalls, incoming)) {
                    continue;
                }
                auto* cached_relocation = alreadyRelocated.lookup(incoming);
                if (cached_relocation != nullptr) {
                    phi.setIncomingValueForBlock(block, cached_relocation);
                } else {
                    builder.SetInsertPoint(block->getTerminator());
                    auto* relocation = relocate(builder,
                        incoming,
                        stackFrameAssignments,
                        stackFramePointers);
                    alreadyRelocated[incoming] = relocation;
                    phi.setIncomingValueForBlock(block, relocation);
                }
            }
        }

        relocatedOutOfBlocks[block] = alreadyRelocated;
    }
}