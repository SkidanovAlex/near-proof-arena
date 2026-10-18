#!/usr/bin/env bash
# One NV layer at the real final-layer protocol settings, scaled to fit <= 16 GB on CPU.
#   ./run_nv_layer.sh <tag> <NV_FIXED heights> [N_STACK] [LOG_BLOWUP] [BITS] [QUERY_POW]
# 268-bit with z = 32 is run as BITS=236 QUERY_POW=0 (the same query counts; the 2^32 grind per
# WHIR round is measured separately by `latency_bench grind`), unless QUERY_POW is given.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
TAG=$1; FIX=$2; NS=${3:-18}; LB=${4:-1}; BITS=${5:-236}; QP=${6:-0}
export NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1 NEARPROOF_TSTAR=1
export PARENT_N_STACK=$NS PARENT_LOG_BLOWUP=$LB PARENT_K=4 PARENT_K1=1 PARENT_BITS=$BITS PARENT_QUERY_POW=$QP \
  PARENT_LIST_M=3 PARENT_X15=15 PARENT_MULTIPROOF=1 PARENT_KEEP_DOMAIN=1 PARENT_GRUEN_GKR=1 PARENT_GKR_DERIVE=1 \
  PARENT_GRUEN_ZC=1 PARENT_NEXT_MASK=1 PARENT_WHIR_Y=1 PARENT_TIGHT=1 PARENT_WIDE_POW=1
export NV_LOG_ROWS=${NV_LOG_ROWS:-18} NV_FIXED=$FIX
mkdir -p "$HERE/logs"
/usr/bin/time -v "$HERE/run_bench.sh" nv_layer > "$HERE/logs/nv-layer-$TAG.log" 2>&1
grep -E "^NVL_|Elapsed|Maximum resident" "$HERE/logs/nv-layer-$TAG.log"
