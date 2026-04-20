#!/usr/bin/bash
set -e
mkdir -p ../.out
cargo build --release
cp target/release/libvega_runtime.a ../.out/libvega_runtime.a
