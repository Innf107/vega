use std::{
    alloc::{Layout, alloc, dealloc},
    debug_assert_matches,
    ptr::{null, null_mut},
};

// This isn't actually accessible to anything outside this module,
// but it still needs to be repr(C) so that we can cast the pointer we have to the
// inner element to a pointer to the actual OwningNode object
#[repr(C)]
struct OwningNode<T> {
    value: T,
    previous: *mut OwningNode<T>,
    next: *mut OwningNode<T>,
}

// Doubly-linked list that owns the memory of its elements.
// This is *not* threadsafe.
pub struct OwningList<T> {
    // This is a cyclical list so we don't have as many edge cases
    first: Option<*mut OwningNode<T>>,
}
impl<T> OwningList<T> {
    pub const fn new() -> Self {
        Self { first: None }
    }

    pub fn append(&mut self, value: T) -> &mut T {
        unsafe {
            let node = alloc(Layout::new::<OwningNode<T>>()).cast::<OwningNode<T>>();
            match self.first {
                None => {
                    *node = OwningNode {
                        value,
                        previous: node,
                        next: node,
                    };
                    self.first = Some(node);
                }
                Some(first) => {
                    *node = OwningNode {
                        value,
                        previous: (*first).previous,
                        next: first,
                    };
                    (*(*first).previous).next = node;
                    (*first).previous = node;
                }
            }
            &mut (*node).value
        }
    }

    /// SAFETY: `pointer` must point to an element of this list obtained by calling `append`.
    /// `pointer` must not accessed in any way after this.
    pub unsafe fn delete_by_pointer(&mut self, pointer: *mut T) {
        unsafe {
            // This is the really unsafe bit but it is okay because OwningNode<T> has repr(C)
            let node = pointer.cast::<OwningNode<T>>();

            (*(*node).next).previous = (*node).previous;
            (*(*node).previous).next = (*node).next;

            debug_assert_matches!(self.first, Some(_));
            if self.first == Some(node) {
                if (*node).next == node {
                    self.first = None
                } else {
                    self.first = Some((*node).next);
                }
            }

            dealloc(node.cast::<u8>(), Layout::new::<OwningNode<T>>());
        }
    }
}

impl<T> Drop for OwningList<T> {
    fn drop(&mut self) {
        todo!()
    }
}
