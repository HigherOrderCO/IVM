#!/usr/bin/env bash
set -Eeuo pipefail

echo "HVM treesum: $(hvm run -f benches/treesum.hvm -t 1 -c true "(Main)" 2>&1 | grep RPS)"
echo "IVM treesum: $(target/release/ivm -i -s benches/treesum.ivm 2>&1 | grep RPS)"

echo "HVM mergesort: $(hvm run -f benches/mergesort.hvm -t 1 -c true "(Main)" 2>&1 | grep RPS)"
echo "IVM mergesort: $(target/release/ivm -i -s benches/mergesort.ivm 2>&1 | grep RPS)"
