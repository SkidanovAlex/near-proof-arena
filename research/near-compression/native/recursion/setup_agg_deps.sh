#!/usr/bin/env bash
# Base/aggregation lane (lane/pq-base-aggregation): the recursion trees of setup_recursion_deps.sh
# plus patches/openvm-recursion-agg.patch (n-to-1 aggregation node, nv/agg.rs) applied on top of
# patches/openvm-recursion-sha384.patch in openvm-sha384.
#
#   NEARPROOF_PQ_DEPS   target root (default /data/illia/nearproof-deps/pq-base-agg; never the
#                       recursion lane's pq-recursion tree)
# Idempotent: an existing overlaid tree is verified (base + overlay reproduce its `git diff`).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-base-agg}
DEPS=$NEARPROOF_PQ_DEPS
case "$DEPS" in */pq-recursion|*/pq-native|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
BASE=$HERE/patches/openvm-recursion-sha384.patch
AGG=$HERE/patches/openvm-recursion-agg.patch
T=$DEPS/openvm-sha384
if [ ! -f "$T/.agg-overlay" ]; then
  "$HERE/setup_recursion_deps.sh"
  git -C "$T" apply "$AGG"
  git -C "$T" add -N .
  touch "$T/.agg-overlay"
fi
# verify: a fresh checkout + base + overlay reproduces the tree's diff
tmp=$(mktemp -d "$DEPS/.verify.XXXX")
trap 'rm -rf "$tmp"' EXIT
git clone -q --no-checkout "$T" "$tmp/t"
git -C "$tmp/t" checkout -q --detach "$(git -C "$T" rev-parse HEAD)"
git -C "$tmp/t" apply "$BASE" 2>/dev/null
git -C "$tmp/t" add -N .
git -C "$tmp/t" apply "$AGG"
git -C "$tmp/t" add -N .
diff <(git -C "$T" diff -- . ':!.agg-overlay' | grep -v '^index ') <(git -C "$tmp/t" diff | grep -v '^index ') >/dev/null \
  || { echo "$T differs from base + agg overlay" >&2; exit 1; }
echo "agg deps OK: $DEPS"
