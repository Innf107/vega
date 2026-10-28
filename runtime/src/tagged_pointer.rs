#[derive(Clone, Copy)]
pub struct TaggedPointer<T, const ALIGNMENT: usize> {
    pointer: *const T,
}
impl<T, const ALIGNMENT: usize> TaggedPointer<T, ALIGNMENT> {
    // We cannot make new const since `pointer.addr` isn't const, even though we only use that in a debug_assert.
    // This function skips that debug_assert so that it can be used in a const context
    pub const fn new_without_assertion(pointer: *const T) -> Self {
        debug_assert!(ALIGNMENT.is_power_of_two());
        Self { pointer }
    }

    pub fn new(pointer: *const T) -> Self {
        debug_assert!(ALIGNMENT.is_power_of_two());
        debug_assert!(pointer.addr().is_multiple_of(ALIGNMENT));
        Self { pointer }
    }

    pub fn pointer(self) -> *const T {
        self.pointer
            .map_addr(|address| address & !((1 << ALIGNMENT.ilog2()) - 1))
    }
    pub fn get_tag<const INDEX: u8>(self) -> bool {
        debug_assert!((1 << INDEX) < ALIGNMENT);

        self.pointer.addr() & (1 << INDEX) != 0
    }
    pub fn set_tag<const INDEX: u8>(self, value: bool) -> Self {
        TaggedPointer {
            pointer: self.pointer.map_addr(|address| {
                if value {
                    address | (1 << INDEX)
                } else {
                    address & !(1 << INDEX)
                }
            }),
        }
    }
}
