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
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/ADT/Twine.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <optional>
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
//
// A freshly constructed bitset represents an infinite sequence of 0s.
class BitSet {
  public:
    void set(unsigned index) {
        if (index >= vector.size()) {
            vector.resize(index + 1);
        };
        vector.set(index);
    }
    bool test(unsigned index) {
        if (index >= vector.size()) {
            return false;
        } else {
            return vector.test(index);
        }
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

    void operator&=(BitSet &other) { vector &= other.vector; }

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

inline bool isGCPointerVariable(Value *value) {
    auto type = value->getType();
    return type->isPointerTy() && type->getPointerAddressSpace() == 1 &&
           !isa<Constant>(value);
}

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

bool isVegaGCCall(Instruction &instruction) {
    if (isa<CallBase>(instruction)) {
        auto *call = dyn_cast<CallBase>(&instruction);
        auto callee = call->getCalledFunction();
        return callee != nullptr && callee->hasGC() &&
               callee->getGC() == "vegagc";
    } else {
        return false;
    }
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

inline bool isGCPointerLiveAcrossCall(PointerIDs &pointerIDs,
                                      BitSet &liveAcrossCalls, Value *value) {
    return isGCPointerVariable(value) &&
           liveAcrossCalls.test(idFor(pointerIDs, value));
}

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

struct StackFrameAssignments {
    DenseMap<Value *, unsigned> assignments;
    unsigned frameSize;
};

StackFrameAssignments
allocateStackFrameSlots(DenseMap<Value *, Interval> intervals) {
    DenseMap<Value *, unsigned> stackSlots;
    unsigned frameSize = 0;

    BitSet usedSlots;

    std::vector<std::pair<Value *, Interval>> sortedIntervals(intervals.begin(),
                                                              intervals.end());
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

        frameSize = std::max(frameSize, slotForThisInterval + 1);
    }

    return StackFrameAssignments{.assignments = stackSlots,
                                 .frameSize = frameSize};
}

void saveToShadowStackIfNecessary(IRBuilder<> &builder,
                                  std::optional<Instruction *> instruction,
                                  PointerIDs pointerIDs, BitSet liveAcrossCalls,
                                  StackFrameAssignments stackFrameAssignments,
                                  Value *stackFramePointers, Value *value) {
    if (isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls, value)) {
        // SAFETY: terminators don't return anything so it's okay to use
        // getNextNode here
        if (instruction.has_value()) {
            auto *nextNonPhiInstruction = instruction.value()->getNextNode();
            while (isa<PHINode>(nextNonPhiInstruction)) {
                nextNonPhiInstruction = nextNonPhiInstruction->getNextNode();
            }
            builder.SetInsertPoint(nextNonPhiInstruction);
        }
        assert(stackFrameAssignments.assignments.contains(value));
        unsigned slot = stackFrameAssignments.assignments.lookup(value);
        auto *stackSlotPointer = builder.CreateGEP(
            PointerType::get(value->getContext(), 1), stackFramePointers,
            {builder.getInt64(slot)}, "stack-slot");
        builder.CreateStore(value, stackSlotPointer);
    }
}

SmallDenseMap<Value *, Value *> intersectionOfPredecessorRelocations(
    BasicBlock *block,
    SmallDenseMap<BasicBlock *, SmallDenseMap<Value *, Value *>>
        &relocatedOutOfBlocks) {
    if (block->hasNPredecessors(0)) {
        return SmallDenseMap<Value *, Value *>();
    }
    if (auto *predecessor = block->getSinglePredecessor()) {
        return relocatedOutOfBlocks[predecessor];
    }

    SmallVector<SmallDenseMap<Value *, Value *>> predecessors;
    for (auto *predecessorBlock : llvm::predecessors(block)) {
        predecessors.push_back(relocatedOutOfBlocks[predecessorBlock]);
    }
    SmallDenseMap<Value *, Value *> intersection;

    for (auto &[k, v] : predecessors[0]) {
        bool is_in_intersection = true;
        for (int i = 1; i < predecessors.size(); i++) {
            if (!predecessors[i].contains(k) || predecessors[i][k] != v) {
                is_in_intersection = false;
                break;
            }
        }
        if (is_in_intersection) {
            intersection[k] = v;
        }
    }
    return intersection;
}
Value *relocate(IRBuilder<> &builder, Value *valueToRelocate,
                StackFrameAssignments &stackFrameAssignments,
                Value *stackFramePointers) {
    assert(stackFrameAssignments.assignments.contains(valueToRelocate));
    unsigned slot = stackFrameAssignments.assignments.lookup(valueToRelocate);

    auto *gcPointerType = PointerType::get(valueToRelocate->getContext(), 1);
    auto *stackSlotPointer =
        builder.CreateGEP(gcPointerType, stackFramePointers,
                          {builder.getInt64(slot)}, "stack-slot");

    return builder.CreateLoad(gcPointerType, stackSlotPointer,
                              valueToRelocate->getName() + ".relocated");
}

// TODO: we need to clear out stack slots once
// they're dead
void saveAndRelocateBoxedPointers(Function &function, PointerIDs pointerIDs,
                                  BitSet liveAcrossCalls,
                                  StackFrameAssignments stackFrameAssignments) {
    if (stackFrameAssignments.frameSize == 0) {
        return;
    }

    auto &context = function.getContext();
    const auto previousShadowStackPointer =
        function.hasParamAttribute(0, Attribute::AttrKind::StructRet)
            ? function.getArg(1)
            : function.getArg(0);

    IRBuilder builder(context);

    builder.SetInsertPointPastAllocas(&function);

    auto *frameStructType = StructType::get(
        context, {// Pointer to the previous segment. This has to be in address
                  // space 0, not 1 since it's not heap allocated itself
                  PointerType::get(context, 0),
                  // Size (doesn't need to be 64 bit but we can't make it less
                  // because of alignment so it doesn't matter)
                  Type::getInt64Ty(context),
                  // The actual pointers. These have to be in address space 1.
                  ArrayType::get(PointerType::get(context, 1),
                                 stackFrameAssignments.frameSize)});
    auto *shadowStackStruct =
        builder.CreateAlloca(frameStructType, nullptr, "shadow-stack-frame");

    // We need to do this before saving the previous pointer, since otherwise
    // that one would be replaced and create a cyclical shadow stack frame
    previousShadowStackPointer->replaceAllUsesWith(shadowStackStruct);

    auto *pointerToPrevious = builder.CreateInBoundsGEP(
        frameStructType, shadowStackStruct,
        {builder.getInt32(0), builder.getInt32(0)}, "previous-slot");
    builder.CreateStore(previousShadowStackPointer, pointerToPrevious);

    auto *pointerToSize = builder.CreateInBoundsGEP(
        frameStructType, shadowStackStruct,
        {builder.getInt32(0), builder.getInt32(1)}, "size-slot");
    builder.CreateStore(builder.getInt64(stackFrameAssignments.frameSize),
                        pointerToSize);

    auto *stackFramePointers = builder.CreateInBoundsGEP(
        frameStructType, shadowStackStruct,
        {builder.getInt32(0), builder.getInt32(2)}, "shadow-stack-pointers");
    builder.CreateMemSetInline(
        stackFramePointers, MaybeAlign(8), builder.getInt8(0),
        builder.getInt64(8 * stackFrameAssignments.frameSize));

    for (Argument &argument : function.args()) {
        saveToShadowStackIfNecessary(builder, std::nullopt, pointerIDs,
                                     liveAcrossCalls, stackFrameAssignments,
                                     stackFramePointers, &argument);
    }

    for (auto &block : function) {
        for (auto &instruction : block) {
            saveToShadowStackIfNecessary(
                builder, std::make_optional(&instruction), pointerIDs,
                liveAcrossCalls, stackFrameAssignments, stackFramePointers,
                &instruction);
        }
    }

    SmallDenseMap<BasicBlock *, SmallDenseMap<Value *, Value *>>
        relocatedOutOfBlocks;

    for (auto *block : depth_first(&function)) {
        SmallDenseMap<Value *, Value *> alreadyRelocated =
            intersectionOfPredecessorRelocations(block, relocatedOutOfBlocks);
        if (block->isEntryBlock()) {
            for (auto &parameter : function.args()) {
                if (isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls,
                                              &parameter)) {
                    alreadyRelocated[&parameter] = &parameter;
                }
            }
        }

        for (auto &instruction : *block) {
            if (isa<PHINode>(instruction)) {
                // We handle phi nodes at the end of their predecessor block
                continue;
            }
            // relocate the operands
            for (auto &operandUse : instruction.operands()) {
                auto *operand = operandUse.get();
                if (!isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls,
                                               operand)) {
                    continue;
                }

                auto *cached_relocation = alreadyRelocated.lookup(operand);
                if (cached_relocation != nullptr) {
                    operandUse.set(cached_relocation);
                } else {

                    builder.SetInsertPoint(&instruction);
                    auto *relocation =
                        relocate(builder, operand, stackFrameAssignments,
                                 stackFramePointers);
                    alreadyRelocated[operand] = relocation;
                    operandUse.set(relocation);
                }
            }

            if (isVegaGCCall(instruction)) {
                // After a gc call, we need to relocate everything again
                alreadyRelocated.clear();
            }

            // The result of an instruction doesn't need to be relocated until
            // we hit a gc call, so we can treat it as if it had already been
            // relocated.
            // It is important that this happens *after* we clear the
            // relocations, since the result of a call does not need to be
            // invalidated
            if (isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls,
                                          &instruction)) {
                alreadyRelocated[&instruction] = &instruction;
            }

            // Tail calls need to be modified to use the previous shadow stack
            // pointer, since our stack frame isn't even alive after the tail
            // call
            if (isa<CallInst>(instruction)) {
                auto* call = dyn_cast<CallInst>(&instruction);
                if (call->isTailCall()) {
                    for (auto &operandUse : call->operands()) {
                        if (operandUse == shadowStackStruct) {
                            operandUse.set(previousShadowStackPointer);
                        }
                    }
                }
            }
        }

        for (auto *successor : successors(block)) {
            for (auto &phi : successor->phis()) {
                auto *incoming = phi.getIncomingValueForBlock(block);
                if (!isGCPointerLiveAcrossCall(pointerIDs, liveAcrossCalls,
                                               incoming)) {
                    continue;
                }
                auto *cached_relocation = alreadyRelocated.lookup(incoming);
                if (cached_relocation != nullptr) {
                    phi.setIncomingValueForBlock(block, cached_relocation);
                } else {
                    builder.SetInsertPoint(block->getTerminator());
                    auto *relocation =
                        relocate(builder, incoming, stackFrameAssignments,
                                 stackFramePointers);
                    alreadyRelocated[incoming] = relocation;
                    phi.setIncomingValueForBlock(block, relocation);
                }
            }
        }

        relocatedOutOfBlocks[block] = alreadyRelocated;
    }
}

}; // namespace llvm

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
}
}
#endif // LLVM_SHADOW_STACK_PLUGIN