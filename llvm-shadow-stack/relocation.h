#pragma once
#include "frame_allocation.h"
#include "pointer_ids.h"
#include <llvm/IR/IRBuilder.h>

using namespace llvm;

void saveToShadowStackIfNecessary(IRBuilder<>& builder,
    std::optional<Instruction*> instruction,
    PointerIDs pointerIDs,
    BitSet liveAcrossCalls,
    StackFrameAssignments stackFrameAssignments,
    Value* stackFramePointers,
    Value* value);

Value* relocate(IRBuilder<>& builder,
    Value* valueToRelocate,
    StackFrameAssignments& stackFrameAssignments,
    Value* stackFramePointers);

void saveAndRelocateBoxedPointers(Function& function,
    PointerIDs pointerIDs,
    BitSet liveAcrossCalls,
    StackFrameAssignments stackFrameAssignments);