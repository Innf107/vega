SECTIONS
{
    .llvm_stackmaps : {
        PROVIDE(__LLVM_STACKMAPS = .);
        KEEP(*(.llvm_stackmaps*))
    }
}
INSERT AFTER .rodata