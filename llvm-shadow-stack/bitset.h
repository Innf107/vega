#pragma once
#include "llvm/ADT/SmallBitVector.h"

using namespace llvm;

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
