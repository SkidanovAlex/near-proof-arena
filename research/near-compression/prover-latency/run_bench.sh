#!/usr/bin/env bash
# Build and run the prover-latency microbenchmarks against this lane's private copy of the
# unified backend + openvm-sha384 trees (rebuilt from the patches at this branch's base).
#   ./run_bench.sh <example> <args...>      example = latency_bench | nv_layer
# Env: RAYON_NUM_THREADS (default 32), NEARPROOF_DIGEST_BYTES / NEARPROOF_COSET_LEAF, HEAVY_MEM (16G).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_LAT_DEPS:-/data/illia/nearproof-deps/pq-latency}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-/data/illia/nearproof-deps/pq-latency-target}
EX=$1; shift
R=$DEPS/openvm-sha384/crates/recursion
mkdir -p "$R/examples"
cp "$HERE/bench/$EX.rs" "$R/examples/$EX.rs"
( cd "$DEPS/openvm-sha384" && cargo build --release -q -p openvm-recursion-circuit --example "$EX" ) > "$DEPS/logs/build-$EX.log" 2>&1 || { tail -30 "$DEPS/logs/build-$EX.log"; exit 1; }
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-32}
HEAVY_MEM=${HEAVY_MEM:-16G} exec taskset -c 0-31 /data/illia/nearproof-deps/bin/heavy "$CARGO_TARGET_DIR/release/examples/$EX" "$@"
