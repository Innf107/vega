#pragma once
#include "llvm/IR/Module.h"
#include <llvm/ADT/DenseMap.h>

using namespace llvm;

struct PointerIDs {
    DenseMap<Value*, unsigned> pointerValueIDs;
    DenseMap<unsigned, Value*> reversePointerValueIDs;
};

unsigned idFor(PointerIDs& pointerIDs, Value* value);
inline bool isGCPointerVariable(Value* value) {
    if (isa<Constant>(value)) {
        return false;
    }
    auto type = value->getType();

    return type->getScalarType()->isPointerTy() &&
        type->getPointerAddressSpace() == 1;
}

bool isVegaGCCall(Instruction& instruction);
