#!/usr/bin/env bash
# lane/pq-nv-preprocessed: the NV deps (setup_recursion_deps.sh) plus the overlay
#   patches/stark-backend-prep.patch     (test_utils: cached traces committed with k1, not k)
#   patches/openvm-recursion-prep.patch  (NV verifies children with preprocessed / cached traces:
#                                         nv/verifier.rs; tests nv/prep_tests.rs, nv/prep_demo.rs)
# applied in place on the recursion crate. Single-commitment children get byte-identical programs.
# Default DEPS keeps this lane's trees apart from the recursion lane's.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-nv-prep}
DEPS=$NEARPROOF_PQ_DEPS
case "$DEPS" in */pq-recursion|*/pq-native|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
if [ ! -f "$DEPS/.prep-overlay" ]; then
  "$HERE/setup_recursion_deps.sh"
  git -C "$DEPS/stark-backend-unified" apply "$HERE/patches/stark-backend-prep.patch"
  git -C "$DEPS/stark-backend-unified" add -N .
  git -C "$DEPS/openvm-sha384" apply "$HERE/patches/openvm-recursion-prep.patch"
  git -C "$DEPS/openvm-sha384" add -N .
  touch "$DEPS/.prep-overlay"
fi
# verify: the overlay regenerated from the live tree equals the pinned patch
CHK=$(mktemp -d); trap 'rm -rf "$CHK"' EXIT
PREP_PATCH_OUT=$CHK "$HERE/make_prep_patches.sh" >/dev/null
for p in stark-backend-prep openvm-recursion-prep; do
  cmp -s "$CHK/$p.patch" "$HERE/patches/$p.patch" || { echo "$p: live tree differs from patch" >&2; exit 1; }
done
echo "prep deps OK: $DEPS"
