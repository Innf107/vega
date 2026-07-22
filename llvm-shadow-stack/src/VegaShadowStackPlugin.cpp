#ifndef LLVM_SHADOW_STACK_PLUGIN
#define LLVM_SHADOW_STACK_PLUGIN

#include "llvm-c/Core.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include <iostream>
#include <llvm-c/Types.h>

using namespace llvm;
namespace llvm {

class ShadowStackPass : public PassInfoMixin<ShadowStackPass> {
  public:
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM) {
        errs() << F.getName() << "\n";
        return PreservedAnalyses::none();
    }
};

} // namespace llvm

extern "C" {
void RunShadowStackPass(LLVMModuleRef moduleRef) {

    std::cout << "LLVM: " << LLVM_VERSION_MAJOR << "." << LLVM_VERSION_MINOR
              << "." << LLVM_VERSION_PATCH << std::endl;

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
            loopAnalysisManager, functionAnalysisManager,
            cgsccAnalysisManager, moduleAnalysisManager);

    // TODO: it would be nice if we could share the analysis managers with the
    // actual optimizations, but that would need us to restructure slightly how
    // the compiler runs these passes.
    ModulePassManager passManager;

    if (auto error = passBuilder.parsePassPipeline(passManager, "vega-shadow-stack")) {
        errs() << "internal shadow stack plugin error: unable to pass pipleine\n";
        consumeError(std::move(error));
        return;
    }
    passManager.run(*module_, moduleAnalysisManager);
}
}

#endif // LLVM_SHADOW_STACK_PLUGIN