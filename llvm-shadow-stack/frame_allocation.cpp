#include "frame_allocation.h"
#include "intervals.h"
#include <llvm/ADT/DenseMap.h>
#include <queue>

using namespace llvm;

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
            usedSlots.reset(stackSlots[inactiveValue]);
        }

        unsigned slotForThisInterval = usedSlots.find_first_unset();
        usedSlots.set(slotForThisInterval);
        stackSlots[value] = slotForThisInterval;
        active.push(std::make_pair(value, interval));

        frameSize = std::max(frameSize, slotForThisInterval + 1);
    }

    return StackFrameAssignments{
        .assignments = stackSlots, .frameSize = frameSize};
}
