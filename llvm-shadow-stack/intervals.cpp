#include "intervals.h"
#include "bitset.h"
#include "liveness.h"
#include "pointer_ids.h"
#include "schedule.h"
#include <llvm/IR/Instructions.h>

using namespace llvm;

DenseMap<Value *, Interval> computeIntervals(
    const Function &function, Schedule &schedule, PointerIDs &pointerIDs,
    DenseMap<BasicBlock *, BitSet> &liveIntoBlock, BitSet liveAcrossCalls) {

    DenseMap<Value *, Interval> intervals;

    for (auto *block : reverse(schedule.blockOrder)) {
        BitSet livePointers;
        for (auto *successor : successors(block)) {
            livePointers |= liveIntoBlock[successor];
            for (auto &phi : successor->phis()) {
                if (isGCPointerVariable(&phi)) {
                    livePointers.set(idFor(
                        pointerIDs, phi.DoPHITranslation(successor, block)));
                }
            }
        }
        unsigned blockStart = schedule.blockStarts[block];
        unsigned blockEnd = schedule.blockEnds[block];
        for (unsigned pointerID : livePointers.set_bits()) {
            if (!liveAcrossCalls.test(pointerID)) {
                continue;
            }
            auto *pointer = pointerIDs.reversePointerValueIDs[pointerID];

            // We initially set the range of every pointer that is live
            // after the block to the entire block. If that's not accurate,
            // we will later refine this with Interval::setFrom.
            intervals[pointer].addRange(blockStart, blockEnd);
        }
        for (auto &instruction : reverse(*block)) {
            if (isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls,
                                          &instruction)) {
                // TODO: we could in principle avoid this hash map lookup if
                // we computed the instruction index from the block indices
                // here
                intervals[&instruction].setFrom(
                    schedule.instructions[&instruction]);
            }
            for (auto &operand : instruction.operands()) {
                auto *value = operand.get();
                if (isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls,
                                              value)) {
                    intervals[value].addRange(
                        blockStart, schedule.instructions[&instruction]);
                }
            }
        }
    }

    return intervals;
}
