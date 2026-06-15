#!/bin/bash
# Run the MetaRocq Animation test suite.
# Tests pass if compilation succeeds (MetaRocq runs at compile time,
# Example assertions use reflexivity which fails on wrong outputs).

set -e

echo "=== MetaRocq Animation Test Suite ==="
echo ""

# Regenerate Makefile.coq from _CoqProject
echo "Generating Makefile.coq..."
coq_makefile -f _CoqProject -o Makefile.coq

# Build everything (including tests)
echo "Building and running tests..."
make -f Makefile.coq -j$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)

echo ""
echo "=== All tests passed ==="
