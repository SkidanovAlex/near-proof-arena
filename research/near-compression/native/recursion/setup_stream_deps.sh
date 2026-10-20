#!/usr/bin/env bash
# lane/pq-stream-commit: the NV deps (setup_recursion_deps.sh) plus the streamed-commitment
# overlay, applied in place on top of the unified backend and the recursion crate:
#   patches/stark-backend-stream.patch    (prover/stream_pcs.rs, hooks in stacked_pcs.rs / whir.rs,
#                                          memprof marks, tests/stream_commit.rs)
#   patches/openvm-recursion-stream.patch (nv/stream_tests.rs; nv_chain saves FINAL.proof + digest)
# Streaming is off unless NEARPROOF_STREAM_COMMIT=1. Default DEPS keeps this lane's trees apart
# from the recursion lane's (/data/illia/nearproof-deps/pq-recursion).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-stream}
DEPS=$NEARPROOF_PQ_DEPS
case "$DEPS" in */pq-recursion|*/pq-native|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
if [ ! -f "$DEPS/.stream-overlay" ]; then
  "$HERE/setup_recursion_deps.sh"
  git -C "$DEPS/stark-backend-unified" apply "$HERE/patches/stark-backend-stream.patch"
  git -C "$DEPS/stark-backend-unified" add -N .
  git -C "$DEPS/openvm-sha384" apply "$HERE/patches/openvm-recursion-stream.patch"
  git -C "$DEPS/openvm-sha384" add -N .
  touch "$DEPS/.stream-overlay"
fi
# verify: the overlay regenerated from the live trees equals the pinned patches
CHK=$(mktemp -d); trap 'rm -rf "$CHK"' EXIT
STREAM_PATCH_OUT=$CHK "$HERE/make_stream_patches.sh" >/dev/null
for p in stark-backend-stream openvm-recursion-stream; do
  cmp -s "$CHK/$p.patch" "$HERE/patches/$p.patch" || { echo "$p: live tree differs from patch" >&2; exit 1; }
done
echo "stream deps OK: $DEPS"
