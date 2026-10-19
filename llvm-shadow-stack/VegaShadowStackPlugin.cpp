#ifndef LLVM_SHADOW_STACK_PLUGIN
#define LLVM_SHADOW_STACK_PLUGIN

#include "bitset.h"
#include "frame_allocation.h"
#include "intervals.h"
#include "liveness.h"
#include "pointer_ids.h"
#include "relocation.h"
#include "schedule.h"

using namespace llvm;

extern "C" {
void RunShadowStackPass(LLVMModuleRef moduleRef) {
    Module *module_ = unwrap(moduleRef);

    for (auto &function : module_->functions()) {
        // We should only process our own functions
        if (!function.hasGC() || function.getGC() != "vegagc") {
            continue;
        }
        if (function.isDeclaration()) {
            continue;
        }

        PointerIDs pointerIDs;
        auto liveIntoBlock = computeLiveness(function, pointerIDs);
        auto liveAcrossCalls =
            filterLiveAcrossGCCalls(function, pointerIDs, liveIntoBlock);
        auto schedule = computeSchedule(function);
        auto intervals = computeIntervals(function, schedule, pointerIDs,
                                          liveIntoBlock, liveAcrossCalls);
        auto StackFrameAssignments = allocateStackFrameSlots(intervals);
        saveAndRelocateBoxedPointers(function, pointerIDs, liveAcrossCalls,
                                     StackFrameAssignments);
    }

    for (auto &function : module_->functions()) {
        // We don't want the gc annotation to stick around since LLVM can't
        // process it.
        // However, we need to do this *after* the actual shadow stack insertion
        // is complete, since we rely on the annotation to determine which calls
        // need to be statepoints. Calls to other functions don't need to save
        // boxed pointers on the shadow stack.
        if (function.hasGC() && function.getGC() == "vegagc") {
            function.clearGC();
        }
    }

    for (auto &function : module_->functions()) {
        for (auto &block : function) {
            for (auto &instruction : make_early_inc_range(block)) {
                auto *callInstruction = dyn_cast<CallInst>(&instruction);
                if (callInstruction == nullptr ||
                    !callInstruction->hasOperandBundles() ||
                    !callInstruction->getOperandBundle(
                        LLVMContext::OB_gc_transition)) {
                    continue;
                }

                CallInst *replacement;

                // We won't ever need any operand bundles other than
                // gc-transition
                assert(!callInstruction->hasOperandBundlesOtherThan(
                    {LLVMContext::OB_gc_transition}));
                replacement = CallInst::Create(callInstruction, {},
                                               callInstruction->getIterator());

                callInstruction->replaceAllUsesWith(replacement);
                callInstruction->eraseFromParent();
            }
        }
    }
}
}
#endif // LLVM_SHADOW_STACK_PLUGIN