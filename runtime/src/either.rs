// why is this not in std??

#[derive(Clone, Copy, Debug)]
pub enum Either<A,B> {
    Left(A),
    Right(B)
}

