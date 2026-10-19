#!/usr/bin/env bash
# pmp.sh <out> <delay> <n> <dt> -- cmd...   (poor man's profiler; LD_PRELOAD allows gdb attach)
OUT=$1 DELAY=$2 N=$3 DT=$4; shift 5
D=$(cd "$(dirname "$0")" && pwd)
LD_PRELOAD=$D/libptracer.so "$@" > "$OUT.prog.log" 2>&1 &
PID=$!
sleep "$DELAY"
: > "$OUT"
for i in $(seq 1 "$N"); do
  kill -0 $PID 2>/dev/null || break
  echo "=== SAMPLE $i $(date +%s)" >> "$OUT"
  gdb -p $PID -batch -nx -ex "set pagination off" -ex "set debuginfod enabled off" -ex "thread apply all bt 24" >> "$OUT" 2>/dev/null
  sleep "$DT"
done
wait $PID
