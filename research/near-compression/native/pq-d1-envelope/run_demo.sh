#!/usr/bin/env bash
# lane/pq-d1-envelope demo: real nearAirV3D1 tables, honest traces of a real D1a fixture,
# proven unchanged on the unified SWIRL backend and verified natively.
#   AIR=<nearAirV3D1.json, the np-lean-export-v3d1 export> run_demo.sh <out_dir> [prove|tamper|check] [tables...]
# deps: setup.sh (own copy of the pq-wasm-base SWIRL tree).  Box rules: 6 threads, heavy wrapper.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
OUT=${1:?out dir}; MODE=${2:-prove}; shift 2 || true
TABLES=${*:-"sha_t sha_r node head val walk uniq ups chacha rng shuf acct akey bnd srcp size qv sort tx akm kib plf rid"}
CASE=${CASE:-$ROOT/oracle/fixtures/v3/public-d1/d1/00-h10007-s3}
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-d1-envelope}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-16G} /data/illia/nearproof-deps/bin/heavy"
mkdir -p "$OUT"
# 1. classical traces (the same generators as `npudr v3d1prove`)
( cd "$ROOT/examples/np-udr-stark-v2/source" && CARGO_TARGET_DIR=$DEPS/target-classical \
  nice -n 10 $HEAVY cargo build --release --offline -j 6 --example d1dump )
# shellcheck disable=SC2086
nice -n 10 $HEAVY "$DEPS/target-classical/release/examples/d1dump" "$AIR" "$CASE" "$OUT/dump" $TABLES
# 2. SWIRL: pre-check, keygen, prove, native verify, V_d statement check (+ tamper cases)
( cd "$HERE" && CARGO_TARGET_DIR=$DEPS/target nice -n 10 $HEAVY cargo build --release --offline -j 6 )
nice -n 10 $HEAVY env RAYON_NUM_THREADS=6 PQD1_DEBUG=1 "$DEPS/target/release/nearproof-pq-d1-envelope" \
  "$AIR" "$OUT/dump" "$MODE" "${SHAPE:-small}" | tee "$OUT/$MODE.log"
