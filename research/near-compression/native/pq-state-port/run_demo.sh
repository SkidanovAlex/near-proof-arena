#!/usr/bin/env bash
# lane/pq-state-port milestone 1: **all 25** nearAirV3 (D0a) tables, honest traces of a real D0a
# fixture, proven unchanged on the unified SWIRL backend and verified natively.  No stand-in tables.
#   AIR=<nearAirV3.json, the np-lean-export-v3 export> run_demo.sh <out_dir> [prove|tamper|check]
# deps: setup.sh (own copy of the pq-wasm-base SWIRL tree).  Box rules: 8 threads, 24 GB, nice 10.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
OUT=${1:?out dir}; MODE=${2:-prove}
CASE=${CASE:-$ROOT/oracle/fixtures/v3/public-d0a/d0/00-h10004-s3}
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-state-port}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-24G} /data/illia/nearproof-deps/bin/heavy"
mkdir -p "$OUT"
# 1. classical traces (the same generators as `npudr v3prove`), re-cut to natural heights >= 4 rows
( cd "$ROOT/examples/np-udr-stark-v2/source" && CARGO_TARGET_DIR=$DEPS/target-classical \
  nice -n 10 $HEAVY cargo build --release --offline -j 8 --example statedump )
nice -n 10 $HEAVY "$DEPS/target-classical/release/examples/statedump" d0a "$AIR" "$CASE" "$OUT/dump"
# 2. SWIRL: pre-check, keygen, prove, native verify, V_d statement check (+ tamper cases)
( cd "$HERE" && CARGO_TARGET_DIR=$DEPS/target nice -n 10 $HEAVY cargo build --release --offline -j 8 )
nice -n 10 $HEAVY env RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} PQD1_DEBUG=1 "$DEPS/target/release/nearproof-pq-state-port" \
  "$AIR" "$OUT/dump" "$MODE" "${VARIANT:-d0a}" "${SHAPE:-small}" | tee "$OUT/$MODE.log"
