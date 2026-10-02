pub struct UnsafeMakeSend<A> {
    contents: A,
}
unsafe impl<A> Send for UnsafeMakeSend<A> {}

impl<A> UnsafeMakeSend<A> {
    pub const fn new(contents: A) -> Self {
        Self { contents }
    }

    pub const unsafe fn get(&self) -> &A {
        &self.contents
    }

    pub const unsafe fn get_mut(&mut self) -> &mut A {
        &mut self.contents
    }

    pub unsafe fn take(self) -> A {
        self.contents
    }
}
