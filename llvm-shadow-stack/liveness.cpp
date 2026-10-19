#include "liveness.h"
#include "bitset.h"
#include "pointer_ids.h"
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/IR/Instructions.h>

using namespace llvm;

DenseMap<BasicBlock *, BitSet> computeLiveness(Function &function,
                                               PointerIDs &pointerIDs) {
    llvm::DenseMap<BasicBlock *, BitSet> genSets;
    llvm::DenseMap<BasicBlock *, BitSet> killSets;

    for (auto *block : post_order(&function)) {
        BitSet genSet;
        BitSet killSet;
        for (auto &instruction : llvm::reverse(*block)) {
            if (isGCPointerVariable(&instruction)) {
                killSet.set(idFor(pointerIDs, &instruction));
            }
            for (auto &operand : instruction.operands()) {
                auto *value = operand.get();
                if (isGCPointerVariable(value)) {
                    genSet.set(idFor(pointerIDs, value));
                }
            }
        }

        genSets[block] = genSet;
        killSets[block] = killSet;
    }

    llvm::DenseMap<BasicBlock *, BitSet> liveIntoBlock;

    bool changed = true;
    while (changed) {
        changed = false;

        // TODO: we might be able to do something smarter than repeatedly
        // looping over all blocks here. This should converge pretty quickly
        // either way though.
        for (auto *block : post_order(&function)) {
            BitSet liveThisIteration;
            for (auto *successor : successors(block)) {
                liveThisIteration |= genSets[successor];
                liveThisIteration -= killSets[successor];
            }
            if (liveIntoBlock[block] != liveThisIteration) {
                changed = true;
                liveIntoBlock[block] = liveThisIteration;
            }
        }
    }

    return liveIntoBlock;
}

// We only need to concern ourselves with boxed pointers that are live across a
// call to a function that could contain a safepoint. Pointers that aren't don't
// need to be stored in the shadow stack.
//
// A bit more formally, a pointer is live across a call, if there is a vegagc
// call instruction such that the pointer is live at the instruction before and
// one after the call.
BitSet filterLiveAcrossGCCalls(Function &function, PointerIDs &pointerIDs,
                               DenseMap<BasicBlock *, BitSet> &liveIntoBlock) {
    BitSet pointersLiveAcrossGCCalls;

    // The order shouldn't matter here since we already have all the block-level
    // liveness information.
    for (auto *block : post_order(&function)) {
        BitSet livePointersAtAll;
        for (auto *successor : successors(block)) {
            livePointersAtAll |= liveIntoBlock[successor];
        }

        for (auto &instruction : reverse(*block)) {
            if (isVegaGCCall(instruction)) {
                BitSet pointersLiveBeforeAndAfterThis = livePointersAtAll;
                if (isGCPointerVariable(&instruction)) {
                    // Any variable in livePointersAtAll is live *after* this
                    // instruction. The variable defined by this call is not
                    // live before it, but every other one is (since it only
                    // becomes dead at its definition), so we only need to
                    // delete one value from the bitset
                    pointersLiveBeforeAndAfterThis.reset(
                        idFor(pointerIDs, &instruction));
                }
                pointersLiveAcrossGCCalls |= pointersLiveBeforeAndAfterThis;
            }

            // It is important that we update this *after* the call check, since
            // we want that one to use the state of the instruction one after
            // this one.
            for (auto &operand : instruction.operands()) {
                auto *value = operand.get();
                if (isGCPointerVariable(value)) {
                    livePointersAtAll.set(idFor(pointerIDs, value));
                }
            }
            if (isGCPointerVariable(&instruction)) {
                livePointersAtAll.reset(idFor(pointerIDs, &instruction));
            }
        }
    }

    return pointersLiveAcrossGCCalls;
}
