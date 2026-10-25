#include "pointer_ids.h"
#include <llvm/IR/Instructions.h>

using namespace llvm;

unsigned idFor(PointerIDs& pointerIDs, Value* value) {
    // TODO: surely there is a way to avoid the double traversal here
    if (pointerIDs.pointerValueIDs.contains(value)) {
        return pointerIDs.pointerValueIDs[value];
    } else {
        unsigned id = pointerIDs.pointerValueIDs.size();
        pointerIDs.pointerValueIDs[value] = id;
        pointerIDs.reversePointerValueIDs[id] = value;
        return id;
    }
}

bool isVegaGCCall(Instruction& instruction) {
    if (isa<CallBase>(instruction)) {
        auto* call = dyn_cast<CallBase>(&instruction);
        auto callee = call->getCalledFunction();
        return callee != nullptr && callee->hasGC() &&
            callee->getGC() == "vegagc";
    } else {
        return false;
    }
}
