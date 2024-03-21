#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

extern void vega_main();

/* Note [Block Layout]:
~~~~~~~~~~~~~~~~~~~~~~~

TAG_BLOCK:
+----[HEADER]----+
| tag            | 1 byte
| size           | 7 bytes
+---[CHILDREN]---+
| BLOCK          | 8 bytes each
| ...            | `size` times
+----------------+

TAG_UNSCANNED:
+----[HEADER]----+
| tag            | 1 byte
| size           | 7 bytes
+---[CHILDREN]---+
| ANYTHING       | 8 * `size` bytes in total
| ...            |
+----------------+

TAG_FORWARD:
+-----[HEADER]-----+
| tag              | 1 bit
| forward address  | 63 bits
+------------------+


`tag` can be one of
    TAG_BLOCK     = 0x00: in this case children should be scanned by the GC
    TAG_UNSCANNED = 0x01: in this case children represent other data
                          (ints, strings, floats, ...) and should not be scanned
                          by the GC
    TAG_FORWARD   = [anything with the lowest bit set]:
                          ONLY USED DURING A RUNNING GC
                          indicates that this block has already been evacuated
                          and the remaining header bits contain the block's new
                          address on the other semispace (shifted to the right
                          by one)

if tag = TAG_BLOCK, there will be `size` children, each of which is an 8 byte
pointer if tag = TAG_UNSCANNED, the children will make up 8 * size bytes but
might not have any coherent structure
*/

#define TAG_BLOCK 0UL
#define TAG_UNSCANNED 1UL
#define TAG_FORWARD (1UL << 63)

void* alloc_semispace_base;
void* alloc_semispace_top;
void* alloc_semispace_ptr;

void* unused_semispace_base;
void* unused_semispace_top;
void* unused_semispace_ptr;

// TODO: scan the stack or something i guess? this really depends on the
// remaining runtime system and stack layout and things
void** roots;
size_t root_count;

// chosen by ✨vibes✨ (i think this is the default page size or something but
// no idea tbqh)
#define INITIAL_SEMISPACE_SIZE 16384

#define VEGA_PANIC(MESSAGE)                                                    \
    fprintf(stderr, "VEGA RTS PANIC: " #MESSAGE);                              \
    exit(1);

#define VEGA_PANICF(MESSAGE, ARGUMENTS)                                        \
    fprintf(stderr, "VEGA RTS PANIC: " #MESSAGE, ARGUMENTS);                   \
    exit(1);

inline size_t vega_get_block_header(void* block) { return ((size_t*)block)[0]; }

inline void vega_set_block_header(void* block, size_t header) {
    ((size_t*)block)[0] = header;
}

inline size_t vega_get_block_tag(size_t header) {
    // See Note [Block Layout]
    return header >> 56;
}

inline size_t vega_get_block_size(size_t header) {
    // See Note [Block Layout]
    return header & 0x00FFFFFFFFFFFFFF;
}

inline void* vega_get_block_child(void* block, size_t child_index) {
    // See Note [Block Layout]
    return ((void**)block)[child_index + 1];
}

inline void vega_set_block_child(void* block, size_t child_index, void* value) {
    // See Note [Block Layout]
    ((void**)block)[child_index + 1] = value;
}

inline size_t vega_is_forward(size_t header) {
    // See Note [Block Layout]
    return header | (1UL << 63);
}

inline size_t vega_get_forward_address(size_t header) {
    // See Note [Block Layout]
    return header << 1;
}

// Evacuate a block and return its new address
void* vega_evacuate(void* block) {
    size_t header = vega_get_block_header(block);

    if (vega_is_forward(header)) {
        // This block has already been evacuated so all we need to do
        // is return the forward address
        return (void*)vega_get_forward_address(header);
    } else {
        void* new_allocation = unused_semispace_ptr;
        size_t block_size = vega_get_block_size(header);
        unused_semispace_ptr += (block_size + 1) * 8;

        ((size_t*)new_allocation)[0] = header;

        if (vega_get_block_tag(header) == TAG_BLOCK) {
            for (size_t i = 0; i < block_size; i++) {
                void* new_address =
                    vega_evacuate(vega_get_block_child(block, i));
                vega_set_block_child(new_allocation, i, new_address);
            }
        } else if (vega_get_block_tag(header) == TAG_UNSCANNED) {
            memcpy(new_allocation + sizeof(header), block + sizeof(header),
                   block_size * 8);
        } else {
            VEGA_PANICF("invalid block tag: %lx", vega_get_block_tag(header));
        }

        // Set the forward address for further evacuations
        vega_set_block_header(block,
                              TAG_FORWARD | (((size_t)new_allocation) >> 1));

        return new_allocation;
    }
}

void vega_collect() {
    // TODO: somehow set up roots i guess
    for (size_t i = 0; i < root_count; i++) {
        vega_evacuate(roots[i]);
    }

    // Swap the base and top pointers
    void* temp = alloc_semispace_base;
    alloc_semispace_base = unused_semispace_base;
    unused_semispace_base = temp;

    temp = alloc_semispace_top;
    alloc_semispace_top = unused_semispace_top;
    unused_semispace_top = alloc_semispace_top;

    alloc_semispace_ptr = unused_semispace_ptr;

    // Reset the size of the (now) unused semispace
    unused_semispace_ptr = unused_semispace_base;
}

void* vega_alloc_raw(size_t size) {
    if (alloc_semispace_ptr + size > alloc_semispace_top) {
        vega_collect();
    }
    if (alloc_semispace_ptr + size > alloc_semispace_top) {
        // TODO: honestly no idea what to do if a collection failed (i guess
        // resize?) so i guess we just panic here for now?
        VEGA_PANIC("still too large for an allocation after collection");
    }

    void* ptr = alloc_semispace_ptr;
    alloc_semispace_ptr += size;
    return ptr;
}

// Allocate a new block with `child_count` children on the heap.
// All children are initially uninitialized and *must* be initialized before the
// next garbage collection.
void* vega_alloc_block(size_t child_count) {
    // See Note [Block Layout]
    void* allocation = vega_alloc_raw((child_count + 1) * 8);

    ((size_t*)allocation)[0] = (TAG_BLOCK << 56) | child_count;

    return allocation;
}

void vega_init() {
    alloc_semispace_base = mmap(NULL, INITIAL_SEMISPACE_SIZE,
                                PROT_READ | PROT_WRITE, MAP_ANONYMOUS, -1, 0);
    alloc_semispace_ptr = alloc_semispace_base;
    alloc_semispace_top = alloc_semispace_base + INITIAL_SEMISPACE_SIZE;

    unused_semispace_base = mmap(NULL, INITIAL_SEMISPACE_SIZE,
                                 PROT_READ | PROT_WRITE, MAP_ANONYMOUS, -1, 0);
    unused_semispace_top = alloc_semispace_base + INITIAL_SEMISPACE_SIZE;
}

int main() {
    vega_init();

    vega_main();
    return 0;
}
