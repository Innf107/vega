#!/usr/bin/bash
set -e
mkdir -p ../.build
cargo build
cp target/debug/libvega_runtime.a ../.build/libvega_runtime.a
