#!/usr/bin/env bash
# lane/pq-stream-commit: prove the real NV FINAL layer on the measured 268-bit A3 fixed-point
# child (lane/pq-recursion-sha384 logs/r268), at a chosen final shape, optionally streamed.
#   run_stream_final.sh <tag> <final_log_blowup> <final_n_stack> <final_k> <final_log_final> <final_list_m> <stream 0|1>
# env: BIN (test binary), A3 (checkpoint), OUT (log dir), HEAVY_MEM (default 90G),
#      NEARPROOF_STREAM_DROP (default 4).
set -uo pipefail
TAG=$1 B=$2 NS=$3 K=$4 LF=$5 M=$6 STREAM=$7
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-stream}
BIN=${BIN:-$DEPS/bin/nv-s1}
A3=${A3:-/data/illia/nearproof-deps/pq-stream-scratch/ckpt/A3.proof}
OUT=${OUT:-/data/illia/nearproof-deps/pq-stream-scratch/$TAG}
mkdir -p "$OUT"
LEV="K1=1 X15=15 KEEP_DOMAIN=1 MULTIPROOF=1 GRUEN_GKR=1 GKR_DERIVE=1 GRUEN_ZC=1 NEXT_MASK=1 WHIR_Y=1 TIGHT=1 WIDE_POW=1 QUERY_POW=32 BITS=268"
P=""; F=""
for x in $LEV; do P="$P PARENT_$x"; F="$F FINAL_$x"; done
cd "$DEPS/openvm-sha384/crates/recursion"
free -g | head -2 > "$OUT/run.log"
env HEAVY_MEM=${HEAVY_MEM:-90G} taskset -c 0-31 /data/illia/nearproof-deps/bin/heavy \
  env RAYON_NUM_THREADS=32 NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1 NEARPROOF_MEMPROF=1 \
  NEARPROOF_STREAM_COMMIT=$STREAM NEARPROOF_STREAM_DROP=${NEARPROOF_STREAM_DROP:-4} \
  NV_LEVELS=0 NV_LOG_ROWS=19 NV_PROG_LOG=18 NV_RESUME_PROOF="$A3" NV_SAVE_DIR="$OUT" \
  PARENT_L_SKIP=2 PARENT_N_STACK=18 PARENT_K=4 PARENT_LOG_BLOWUP=2 PARENT_LIST_M=3 PARENT_LOG_FINAL=3 $P \
  FINAL_LOG_BLOWUP=$B FINAL_L_SKIP=2 FINAL_N_STACK=$NS FINAL_K=$K FINAL_LOG_FINAL=$LF FINAL_LIST_M=$M $F \
  /usr/bin/time -v "$BIN" nv::tests::nv_chain --ignored --exact --nocapture --test-threads 1 >> "$OUT/run.log" 2>&1
echo "EXIT $?" >> "$OUT/run.log"
