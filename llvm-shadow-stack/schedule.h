#pragma once
#include "llvm/IR/Module.h"

using namespace llvm;

// A schedule fixes an order of instructions. This allows us to define
// live ranges that span across basic blocks.
struct Schedule {
    DenseMap<Instruction*, unsigned> instructions;
    DenseMap<BasicBlock*, unsigned> blockStarts;
    DenseMap<BasicBlock*, unsigned> blockEnds;
    std::vector<BasicBlock*> blockOrder;
};

Schedule computeSchedule(Function& function);
