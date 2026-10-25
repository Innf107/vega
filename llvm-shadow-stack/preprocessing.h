#include <llvm/IR/Function.h>

using namespace llvm;

void fixSRetAllocas(Function& function);

// TODO: track vectors of pointers
