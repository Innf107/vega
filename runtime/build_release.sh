#!/usr/bin/bash
set -e
mkdir -p ../.build
cargo build --release
cp target/release/libvega_runtime.a ../.build/libvega_runtime.a
