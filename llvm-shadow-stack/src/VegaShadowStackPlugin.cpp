#ifndef LLVM_SHADOW_STACK_PLUGIN
#define LLVM_SHADOW_STACK_PLUGIN

#include "llvm-c/Core.h"
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
        function.clearGC();

        if (function.isDeclaration()) {
            return PreservedAnalyses::all();
        }

        const auto previousShadowStackPointer =
            function.hasAttributeAtIndex(0, Attribute::AttrKind::StructRet)
                ? function.getArg(1)
                : function.getArg(0);

        IRBuilder builder(context);

        builder.SetInsertPoint(&function.getEntryBlock(), function.getEntryBlock().getFirstInsertionPt());
        auto shadow_stack_alloca = builder.CreateAlloca(
            PointerType::get(context, 0),
            ConstantInt::get(Type::getInt64Ty(context), 0), "shadow_stack");

        return PreservedAnalyses::none();
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