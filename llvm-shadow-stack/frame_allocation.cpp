#include "frame_allocation.h"
#include "intervals.h"
#include <llvm/ADT/DenseMap.h>
#include <queue>

using namespace llvm;

unsigned vectorSize(Value* pointer) {
    auto* type = pointer->getType();
    if (type->isVectorTy()) {
        assert(isa<FixedVectorType>(type));
        auto* vectorType = dyn_cast<FixedVectorType>(type);
        return vectorType->getNumElements();
    } else {
        return 1;
    }
}

StackFrameAssignments allocateStackFrameSlots(
    DenseMap<Value*, Interval> intervals) {
    DenseMap<Value*, unsigned> stackSlots;
    unsigned frameSize = 0;

    BitSet usedSlots;

    std::vector<std::pair<Value*, Interval>> sortedIntervals(
        intervals.begin(), intervals.end());
    llvm::sort(sortedIntervals, [](auto& pair1, auto& pair2) {
        return pair1.second.from < pair2.second.from;
    });

    auto increasingEndpoint = [](auto& interval1, auto& interval2) {
        return interval1.second.to < interval2.second.to;
    };
    std::priority_queue<std::pair<Value*, Interval>,
        llvm::SmallVector<std::pair<Value*, Interval>>,
        decltype(increasingEndpoint)>
        active;

    for (auto& [value, interval] : sortedIntervals) {
        while (!active.empty()) {
            if (active.top().second.to >= interval.from) {
                break;
            }
            auto [inactiveValue, inactiveInterval] = active.top();
            active.pop();

            assert(stackSlots.contains(inactiveValue));
            usedSlots.reset_range(
                stackSlots[inactiveValue], vectorSize(inactiveValue));
        }

        unsigned slotForThisInterval =
            usedSlots.find_unset_range_of_size(vectorSize(value));
        usedSlots.set_range(slotForThisInterval, vectorSize(value));
        stackSlots[value] = slotForThisInterval;
        active.push(std::make_pair(value, interval));

        frameSize = std::max(frameSize, slotForThisInterval + vectorSize(value));
    }

    return StackFrameAssignments{
        .assignments = stackSlots, .frameSize = frameSize};
}
