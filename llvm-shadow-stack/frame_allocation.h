#pragma once
#include "intervals.h"
#include <llvm/ADT/DenseMap.h>

using namespace llvm;

struct StackFrameAssignments {
    DenseMap<Value *, unsigned> assignments;
    unsigned frameSize;
};

StackFrameAssignments
allocateStackFrameSlots(DenseMap<Value *, Interval> intervals);