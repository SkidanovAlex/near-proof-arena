#!/usr/bin/env bash
# lane/pq-cpu-prover: build and run a bench example (bench/<example>.rs) against this lane's deps tree
# (setup_cpu_fast_deps.sh; default /data/illia/nearproof-deps/pq-cpu).
#   ./run_bench.sh <example> <args...>      example = nv_layer | latency_bench | ext12_bench
# Env: RAYON_NUM_THREADS (default 8), HEAVY_MEM (default 24G), CPUS (taskset list, default 0-7),
#      FAST_RUSTFLAGS (default "-C target-cpu=native"; set empty for the generic x86-64 build),
#      CARGO_TARGET_DIR (default .../pq-cpu-target, or .../pq-cpu-target-generic without FAST_RUSTFLAGS),
#      BUILD_ONLY=1, NICE (default 10).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-cpu}
FAST_RUSTFLAGS=${FAST_RUSTFLAGS--C target-cpu=native}
if [ -n "$FAST_RUSTFLAGS" ]; then DT=/data/illia/nearproof-deps/pq-cpu-target; else DT=/data/illia/nearproof-deps/pq-cpu-target-generic; fi
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$DT}
EX=$1; shift
R=$DEPS/openvm-sha384/crates/recursion
mkdir -p "$R/examples" "$DEPS/logs"
cmp -s "$HERE/bench/$EX.rs" "$R/examples/$EX.rs" || cp "$HERE/bench/$EX.rs" "$R/examples/$EX.rs"
( cd "$DEPS/openvm-sha384" && CARGO_PROFILE_RELEASE_STRIP=false CARGO_PROFILE_RELEASE_DEBUG=line-tables-only RUSTFLAGS="$FAST_RUSTFLAGS -C link-arg=-fuse-ld=mold" HEAVY_MEM=${BUILD_MEM:-20G} \
    nice -n 10 /data/illia/nearproof-deps/bin/heavy cargo build --release -q -j 8 -p openvm-recursion-circuit --example "$EX" ) \
  > "$DEPS/logs/build-$EX.log" 2>&1 || { tail -30 "$DEPS/logs/build-$EX.log"; exit 1; }
[ "${BUILD_ONLY:-0}" = 1 ] && { echo "$CARGO_TARGET_DIR/release/examples/$EX"; exit 0; }
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
HEAVY_MEM=${HEAVY_MEM:-24G} exec nice -n ${NICE:-10} taskset -c ${CPUS:-0-7} /data/illia/nearproof-deps/bin/heavy "$CARGO_TARGET_DIR/release/examples/$EX" "$@"
