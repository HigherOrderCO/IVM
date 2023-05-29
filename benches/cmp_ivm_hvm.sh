#!/usr/bin/env bash
set -Eeuo pipefail

time (hvm run -f benches/treesum.hvm -t 1 -c true "(Main)" | grep RPS) &
time (target/release/ivm benches/treesum.ivm | grep RPS) &
wait
