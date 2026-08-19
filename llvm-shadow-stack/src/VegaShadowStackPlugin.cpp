#ifndef LLVM_SHADOW_STACK_PLUGIN
#define LLVM_SHADOW_STACK_PLUGIN

#include "llvm-c/Core.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include <iostream>
#include <llvm-c/Types.h>
#include <queue>

using namespace llvm;
namespace llvm {

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

// Wrapper around a SmallBitVector that allows setting bits at any index
// without a fixed length.
class BitSet {
  public:
    void set(unsigned index) {
        if (index >= vector.size()) {
            vector.resize(index + 1);
        };
        vector.set(index);
    }
    void reset(unsigned index) {
        // If the index is out of bounds of the underlying vector, it is
        // implicitly 0 anyway.
        if (index < vector.size()) {
            vector.reset(index);
        }
    }

    unsigned find_first_unset() {
        int in_underlying = vector.find_first_unset();
        if (in_underlying == -1) {
            // all bits in the underlying vector are set, but the next bit after
            // that is implicitly 0
            return vector.size();
        } else {
            return (unsigned)in_underlying;
        }
    }

    void operator|=(BitSet &other) {
        if (other.vector.size() > vector.size()) {
            vector.resize(other.vector.size());
        }
        vector |= other.vector;
    }

    void operator-=(BitSet &other) {
        // his could be asymptotically faster but that doesn't matter
        // unless other has more than 63 entries and the ~ needs a
        // memory allocation (which is extremely unlikely)
        vector &= ~other.vector;
    }

    bool operator==(BitSet &other) {
        if (vector.size() == other.vector.size()) {
            return vector == other.vector;
        } else {
            return vector.subsetOf(other.vector) ||
                   other.vector.subsetOf(vector);
        }
    }

    bool operator!=(BitSet &other) { return !this->operator==(other); }

    iterator_range<llvm::SmallBitVector::const_set_bits_iterator>
    set_bits() const {
        return vector.set_bits();
    }

  private:
    SmallBitVector vector;
};

struct PointerIDs {
    DenseMap<Value *, unsigned> pointerValueIDs;
    DenseMap<unsigned, Value *> reversePointerValueIDs;
};

// A schedule fixes an order of instructions. This allows us to define
// live ranges that span across basic blocks.
struct Schedule {
    DenseMap<Instruction *, unsigned> instructions;
    DenseMap<BasicBlock *, unsigned> blockStarts;
    DenseMap<BasicBlock *, unsigned> blockEnds;
    std::vector<BasicBlock *> blockOrder;
};

class ShadowStackPass : public PassInfoMixin<ShadowStackPass> {
  public:
    PreservedAnalyses run(Function &function, FunctionAnalysisManager &AM) {
        auto &context = function.getContext();
        // We should only process our own functions
        if (function.getGC() != "vegagc") {
            return PreservedAnalyses::all();
        }
        // We don't want the gc annotation to stick around since LLVM can't
        // process it
        // TODO: this doesn't work. we can only clear the gc annotation after we
        // have already processed all calls to it that need to preserve it. In
        // fact, we should probably just use a pass over the entire module,
        // rather than one on functions
        function.clearGC();

        if (function.isDeclaration()) {
            return PreservedAnalyses::all();
        }

        outs() << "<<<" << function.getName() << ">>>\n";

        PointerIDs pointerIDs;
        auto livePointersInBlock = computeLiveness(function, pointerIDs);
        auto schedule = computeSchedule(function);
        auto intervals = computeIntervals(function, schedule, pointerIDs,
                                          livePointersInBlock);
        auto slotAssignments = allocateStackFrameSlots(intervals);

        const auto previousShadowStackPointer =
            function.hasAttributeAtIndex(0, Attribute::AttrKind::StructRet)
                ? function.getArg(1)
                : function.getArg(0);

        IRBuilder builder(context);

        builder.SetInsertPoint(&function.getEntryBlock(),
                               function.getEntryBlock().getFirstInsertionPt());
        auto shadow_stack_alloca =
            builder.CreateAlloca(PointerType::get(context, 0),
                                 ConstantInt::get(Type::getInt64Ty(context), 0),
                                 "shadow-stack-frame");

        return PreservedAnalyses::none();
    }

  private:
    unsigned idFor(PointerIDs &pointerIDs, Value *value) {
        // TODO: surely there is a way to avoid the double traversal here
        if (pointerIDs.pointerValueIDs.contains(value)) {
            return pointerIDs.pointerValueIDs[value];
        } else {
            unsigned id = pointerIDs.pointerValueIDs.size();
            pointerIDs.pointerValueIDs[value] = id;
            pointerIDs.reversePointerValueIDs[id] = value;
            return id;
        }
    }

    inline bool isGCPointer(Value *value) {
        auto type = value->getType();
        return type->isPointerTy() && type->getPointerAddressSpace() == 1;
    }

    DenseMap<BasicBlock *, BitSet> computeLiveness(Function &function,
                                                   PointerIDs &pointerIDs) {
        llvm::DenseMap<BasicBlock *, BitSet> genSets;
        llvm::DenseMap<BasicBlock *, BitSet> killSets;

        for (auto *block : post_order(&function)) {
            BitSet genSet;
            BitSet killSet;
            for (auto &instruction : llvm::reverse(*block)) {
                if (isGCPointer(&instruction)) {
                    killSet.set(idFor(pointerIDs, &instruction));
                }
                for (auto &operand : instruction.operands()) {
                    auto *value = operand.get();
                    if (isGCPointer(value)) {
                        genSet.set(idFor(pointerIDs, value));
                    }
                }
            }

            genSets[block] = genSet;
            killSets[block] = killSet;
        }

        llvm::DenseMap<BasicBlock *, BitSet> livePointersPerBlock;

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
                if (livePointersPerBlock[block] != liveThisIteration) {
                    changed = true;
                    livePointersPerBlock[block] = liveThisIteration;
                }
            }
        }

        return livePointersPerBlock;
    }

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

    DenseMap<Value *, Interval>
    computeIntervals(Function &function, Schedule &schedule,
                     PointerIDs &pointerIDs,
                     DenseMap<BasicBlock *, BitSet> livePointersInBlock) {
        DenseMap<Value *, Interval> intervals;

        for (auto *block : reverse(schedule.blockOrder)) {
            BitSet livePointers;
            for (auto *successor : successors(block)) {
                livePointers |= livePointersInBlock[successor];
                for (auto &phi : successor->phis()) {
                    if (isGCPointer(&phi)) {
                        livePointers.set(
                            idFor(pointerIDs,
                                  phi.DoPHITranslation(successor, block)));
                    }
                }
            }
            unsigned blockStart = schedule.blockStarts[block];
            unsigned blockEnd = schedule.blockEnds[block];
            for (unsigned pointerID : livePointers.set_bits()) {
                auto *pointer = pointerIDs.reversePointerValueIDs[pointerID];

                // We initially set the range of every pointer that is live
                // after the block to the entire block. If that's not accurate,
                // we will later refine this with Interval::setFrom.
                intervals[pointer].addRange(blockStart, blockEnd);
            }
            for (auto &instruction : reverse(*block)) {
                if (isGCPointer(&instruction)) {
                    // TODO: we could in principle avoid this hash map lookup if
                    // we computed the instruction index from the block indices
                    // here
                    intervals[&instruction].setFrom(
                        schedule.instructions[&instruction]);
                }
                for (auto &operand : instruction.operands()) {
                    auto *value = operand.get();
                    if (isGCPointer(value)) {
                        intervals[value].addRange(
                            blockStart, schedule.instructions[&instruction]);
                    }
                }
            }
        }

        return intervals;
    }

    DenseMap<Value *, unsigned>
    allocateStackFrameSlots(DenseMap<Value *, Interval> intervals) {
        DenseMap<Value *, unsigned> stackSlots;

        BitSet usedSlots;

        std::vector<std::pair<Value *, Interval>> sortedIntervals(
            intervals.begin(), intervals.end());
        llvm::sort(sortedIntervals, [](auto &pair1, auto &pair2) {
            return pair1.second.from < pair2.second.from;
        });

        auto increasingEndpoint = [](auto &interval1, auto &interval2) {
            return interval1.second.to < interval2.second.to;
        };
        std::priority_queue<std::pair<Value *, Interval>,
                            llvm::SmallVector<std::pair<Value *, Interval>>,
                            decltype(increasingEndpoint)>
            active;

        for (auto &[value, interval] : sortedIntervals) {
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
        }

        return stackSlots;
    }
};
} // namespace llvm

extern "C" {
void RunShadowStackPass(LLVMModuleRef moduleRef) {
    Module *module_ = unwrap(moduleRef);

    PassBuilder passBuilder;
    passBuilder.registerPipelineParsingCallback(
        [](StringRef name, FunctionPassManager &functionManager,
           ArrayRef<PassBuilder::PipelineElement> _) {
            if (name == "vega-shadow-stack") {
                functionManager.addPass(ShadowStackPass());
                return true;
            } else {
                return false;
            }
        });

    LoopAnalysisManager loopAnalysisManager;
    passBuilder.registerLoopAnalyses(loopAnalysisManager);
    FunctionAnalysisManager functionAnalysisManager;
    passBuilder.registerFunctionAnalyses(functionAnalysisManager);
    CGSCCAnalysisManager cgsccAnalysisManager;
    passBuilder.registerCGSCCAnalyses(cgsccAnalysisManager);
    ModuleAnalysisManager moduleAnalysisManager;
    passBuilder.registerModuleAnalyses(moduleAnalysisManager);

    passBuilder.crossRegisterProxies(
        loopAnalysisManager, functionAnalysisManager, cgsccAnalysisManager,
        moduleAnalysisManager);

    // TODO: it would be nice if we could share the analysis managers with the
    // actual optimizations, but that would need us to restructure slightly how
    // the compiler runs these passes.
    ModulePassManager passManager;

    if (auto error =
            passBuilder.parsePassPipeline(passManager, "vega-shadow-stack")) {
        errs()
            << "internal shadow stack plugin error: unable to pass pipleine\n";
        consumeError(std::move(error));
        return;
    }
    passManager.run(*module_, moduleAnalysisManager);
}
}

#endif // LLVM_SHADOW_STACK_PLUGIN