#pragma once
#include "bitset.h"
#include "pointer_ids.h"
#include "llvm/IR/Module.h"

using namespace llvm;

DenseMap<BasicBlock*, BitSet> computeLiveness(
    Function& function, PointerIDs& pointerIDs);

// We only need to concern ourselves with boxed pointers that are live across a
// call to a function that could contain a safepoint. Pointers that aren't don't
// need to be stored in the shadow stack.
//
// A bit more formally, a pointer is live across a call, if there is a vegagc
// call instruction such that the pointer is live at the instruction before and
// one after the call.
BitSet filterLiveAcrossGCCalls(Function& function,
    PointerIDs& pointerIDs,
    DenseMap<BasicBlock*, BitSet>& liveIntoBlock);

inline bool isGCPointerLiveAcrossCall(
    PointerIDs& pointerIDs, BitSet& liveAcrossCalls, Value* value) {
    return isGCPointerVariable(value) &&
        liveAcrossCalls.test(idFor(pointerIDs, value));
}
