#include "schedule.h"
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/IR/Instructions.h>

using namespace llvm;

Schedule computeSchedule(Function &function) {
    Schedule schedule;
    unsigned current_index = 0;
    for (auto *block : ReversePostOrderTraversal(&function)) {
        schedule.blockOrder.push_back(block);
        schedule.blockStarts[block] = current_index;
        current_index++;
        for (auto &instruction : *block) {
            schedule.instructions[&instruction] = current_index;
            current_index++;
        }
        schedule.blockEnds[block] = current_index;
    }
    return schedule;
}
