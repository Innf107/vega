#ifndef LLVM_SHADOW_STACK_PLUGIN
#define LLVM_SHADOW_STACK_PLUGIN

#include "llvm-c/Core.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include <iostream>
#include <llvm-c/Types.h>

using namespace llvm;
namespace llvm {

class ShadowStackPass : public PassInfoMixin<ShadowStackPass> {
  public:
    PreservedAnalyses run(Function &function, FunctionAnalysisManager &AM) {
        auto &context = function.getContext();
        // We should only process our own functions
        if (function.getGC() != "vegagc") {
            return PreservedAnalyses::all();
        }
        // We don't want the gc annotation to stick around since LLVM can't
        // process it
        // TODO: this doesn't work. we can only clear the gc annotation after we
        // have already processed all calls to it that need to preserve it. In
        // fact, we should probably just use a pass over the entire module,
        // rather than one on functions
        function.clearGC();

        if (function.isDeclaration()) {
            return PreservedAnalyses::all();
        }

        auto livePointersPerBlock = computeLiveness(function);

        const auto previousShadowStackPointer =
            function.hasAttributeAtIndex(0, Attribute::AttrKind::StructRet)
                ? function.getArg(1)
                : function.getArg(0);

        IRBuilder builder(context);

        builder.SetInsertPoint(&function.getEntryBlock(),
                               function.getEntryBlock().getFirstInsertionPt());
        auto shadow_stack_alloca =
            builder.CreateAlloca(PointerType::get(context, 0),
                                 ConstantInt::get(Type::getInt64Ty(context), 0),
                                 "shadow-stack-frame");

        return PreservedAnalyses::none();
    }

  private:
    DenseMap<Value *, unsigned> pointerValueIDs;
    DenseMap<unsigned, Value *> reversePointerValueIDs;

    unsigned idFor(Value *value) {
        // TODO: surely there is a way to avoid the double traversal here
        if (pointerValueIDs.contains(value)) {
            return pointerValueIDs[value];
        } else {
            unsigned id = pointerValueIDs.size();
            pointerValueIDs[value] = id;
            reversePointerValueIDs[id] = value;
            return id;
        }
    }

    inline bool isGCPointer(Value *value) {
        auto type = value->getType();
        return type->isPointerTy() && type->getPointerAddressSpace() == 1;
    }

    DenseMap<BasicBlock *, llvm::SmallBitVector>
    computeLiveness(Function &function) {
        llvm::DenseMap<BasicBlock *, llvm::SmallBitVector> genSets;
        llvm::DenseMap<BasicBlock *, llvm::SmallBitVector> killSets;

        for (auto *block : post_order(&function)) {
            llvm::SmallBitVector genSet;
            llvm::SmallBitVector killSet;
            for (auto &instruction : llvm::reverse(*block)) {
                if (isGCPointer(&instruction)) {
                    killSet.set(idFor(&instruction));
                }
                for (auto &operand : instruction.operands()) {
                    auto *value = operand.get();
                    if (isGCPointer(value)) {
                        genSet.set(idFor(value));
                    }
                }
            }

            genSets[block] = genSet;
            killSets[block] = killSet;
        }

        llvm::DenseMap<BasicBlock *, llvm::SmallBitVector> livePointersPerBlock;

        bool changed = true;
        while (changed) {
            changed = false;

            // TODO: we might be able to do something smarter than repeatedly
            // looping over all blocks here. This should converge pretty quickly
            // either way though.
            for (auto *block : post_order(&function)) {
                SmallBitVector liveThisIteration;
                for (auto *successor : successors(block)) {
                    liveThisIteration |= genSets[successor];
                    liveThisIteration &= ~killSets[successor];
                }
                if (livePointersPerBlock[block] != liveThisIteration) {
                    changed = true;
                    livePointersPerBlock[block] = liveThisIteration;
                }
            }
        }

        return livePointersPerBlock;
    }
};
} // namespace llvm

extern "C" {
void RunShadowStackPass(LLVMModuleRef moduleRef) {
    Module *module_ = unwrap(moduleRef);

    PassBuilder passBuilder;
    passBuilder.registerPipelineParsingCallback(
        [](StringRef name, FunctionPassManager &functionManager,
           ArrayRef<PassBuilder::PipelineElement> _) {
            if (name == "vega-shadow-stack") {
                functionManager.addPass(ShadowStackPass());
                return true;
            } else {
                return false;
            }
        });

    LoopAnalysisManager loopAnalysisManager;
    passBuilder.registerLoopAnalyses(loopAnalysisManager);
    FunctionAnalysisManager functionAnalysisManager;
    passBuilder.registerFunctionAnalyses(functionAnalysisManager);
    CGSCCAnalysisManager cgsccAnalysisManager;
    passBuilder.registerCGSCCAnalyses(cgsccAnalysisManager);
    ModuleAnalysisManager moduleAnalysisManager;
    passBuilder.registerModuleAnalyses(moduleAnalysisManager);

    passBuilder.crossRegisterProxies(
        loopAnalysisManager, functionAnalysisManager, cgsccAnalysisManager,
        moduleAnalysisManager);

    // TODO: it would be nice if we could share the analysis managers with the
    // actual optimizations, but that would need us to restructure slightly how
    // the compiler runs these passes.
    ModulePassManager passManager;

    if (auto error =
            passBuilder.parsePassPipeline(passManager, "vega-shadow-stack")) {
        errs()
            << "internal shadow stack plugin error: unable to pass pipleine\n";
        consumeError(std::move(error));
        return;
    }
    passManager.run(*module_, moduleAnalysisManager);
}
}

#endif // LLVM_SHADOW_STACK_PLUGIN