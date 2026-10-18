#!/usr/bin/env bash
# pq-e2e-slice lane (lane/pq-e2e-slice): the recursion trees of setup_recursion_deps.sh plus
# patches/openvm-recursion-e2e.patch (nv/e2e.rs: base AIR set, chunk claim, V_d; nv/e2e_tests.rs;
# nv/e2e_literal_gen.rs) applied on top of patches/openvm-recursion-sha384.patch in openvm-sha384.
#
#   NEARPROOF_PQ_DEPS   target root (default /data/illia/nearproof-deps/pq-e2e; never another
#                       lane's tree)
#   E2E_REFRESH=1       regenerate patches/openvm-recursion-e2e.patch from the tree (author mode)
# Idempotent: an existing overlaid tree is verified (base + overlay reproduce its `git diff`).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e}
DEPS=$NEARPROOF_PQ_DEPS
case "$DEPS" in */pq-recursion|*/pq-base-agg|*/pq-native|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
BASE=$HERE/patches/openvm-recursion-sha384.patch
E2E=$HERE/patches/openvm-recursion-e2e.patch
T=$DEPS/openvm-sha384
FILES="crates/recursion/src/nv/mod.rs crates/recursion/src/nv/e2e.rs crates/recursion/src/nv/e2e_tests.rs crates/recursion/src/nv/e2e_literal_gen.rs"
base_clone() {  # <dir>: fresh checkout of the tree's revision + base patch
  git clone -q --no-checkout "$T" "$1"
  git -C "$1" checkout -q --detach "$(git -C "$T" rev-parse HEAD)"
  git -C "$1" apply "$BASE" 2>/dev/null
  git -C "$1" add -N .
}
tmp=$(mktemp -d "$DEPS/.e2e.XXXX")
trap 'rm -rf "$tmp"' EXIT
if [ "${E2E_REFRESH:-0}" = 1 ]; then
  base_clone "$tmp/b"
  git -C "$tmp/b" add -A . && git -C "$tmp/b" -c user.name=e2e -c user.email=e2e@localhost commit -q -m base
  for f in $FILES; do cp "$T/$f" "$tmp/b/$f"; done
  git -C "$tmp/b" add -N . && git -C "$tmp/b" diff > "$E2E"
  echo "wrote $E2E"
  exit 0
fi
if [ ! -f "$T/.e2e-overlay" ]; then
  "$HERE/setup_recursion_deps.sh"
  git -C "$T" apply "$E2E"
  git -C "$T" add -N .
  touch "$T/.e2e-overlay"
fi
base_clone "$tmp/t"
git -C "$tmp/t" apply "$E2E"
git -C "$tmp/t" add -N .
diff <(git -C "$T" diff -- . ':!.e2e-overlay' | grep -v '^index ') <(git -C "$tmp/t" diff | grep -v '^index ') >/dev/null \
  || { echo "$T differs from base + e2e overlay" >&2; exit 1; }
echo "e2e deps OK: $DEPS"
