#pragma once
#include "bitset.h"
#include "liveness.h"
#include "pointer_ids.h"
#include "schedule.h"
#include "llvm-c/Core.h"

using namespace llvm;

struct Interval {
  public:
    // We use (-1, -1) as a sentinel value for an uninitialized interval
    int from = -1;
    int to = -1;

    bool isUninitialized() { return from == -1 && to == -1; }

    void addRange(int newFrom, int newTo) {
        assert(newFrom < newTo);
        if (isUninitialized()) {
            from = newFrom;
            to = newTo;
        } else {
            from = std::min(from, newFrom);
            to = std::max(to, newTo);
        }
    }

    void setFrom(int newFrom) {
        if (isUninitialized()) {
            from = newFrom;
            // TODO: doesn't this conflict with our invariant that to is
            // *strictly* larger than from?
            to = newFrom;
        } else {
            assert(newFrom < to);
            from = newFrom;
        }
    }
};

DenseMap<Value *, Interval> computeIntervals(
    const Function &function, Schedule &schedule, PointerIDs &pointerIDs,
    DenseMap<BasicBlock *, BitSet> &liveIntoBlock, BitSet liveAcrossCalls);