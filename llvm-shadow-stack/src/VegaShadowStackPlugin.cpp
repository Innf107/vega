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

  std::cout << "LLVM: " << LLVM_VERSION_MAJOR << "." << LLVM_VERSION_MINOR << "." << LLVM_VERSION_PATCH << std::endl;

  Module *module_ = unwrap(moduleRef);

  ModulePassManager passManager;
  passManager.addPass(createModuleToFunctionPassAdaptor(ShadowStackPass()));

  // TODO: it would be nice if we could share this analysisManager with the
  // actual optimizations, but that would need us to restructure slightly how
  // the compiler runs these passes.
  ModuleAnalysisManager analysisManager;

  passManager.run(*module_, analysisManager);
}
}

#endif // LLVM_SHADOW_STACK_PLUGIN