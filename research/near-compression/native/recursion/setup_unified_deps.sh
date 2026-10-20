#!/usr/bin/env bash
# Unified research backend for NV (lane/pq-recursion-sha384):
#   pinned stark-backend d667af5 + native base patch (native/setup_native_deps.sh tree)
#   + patches/stark-backend-unified.patch = lane/pq-whir-levers stark-backend-levers.patch (ab3cfd969)
#     merged with lane/pq-x15-domains stark-backend-x15.patch (2cf46f1a4), conflicts resolved,
#     plus x15 x coset-leaf (MerkleTree::new_with_cosets hashes fold cosets with hash_coset) and
#     x15 x multiproof (depth + ceil_log2(c)) fixes, plus later NV-lane additions (see README).
# Every lever is default-off; gas-failure5 re-proves byte-identically at defaults.
# Target: $DEPS/stark-backend-unified (DEPS default /data/illia/nearproof-deps/pq-recursion).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-recursion}
case "$DEPS" in */pq-native|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
B=$DEPS/stark-backend
U=$DEPS/stark-backend-unified
P=$HERE/patches/stark-backend-unified.patch
[ -d "$B/.git" ] || { echo "run setup_recursion_deps.sh first" >&2; exit 1; }
if [ ! -d "$U/.git" ]; then
  cp -a "$B" "$U"; rm -rf "$U/target"
  git -C "$U" -c user.name=nearproof -c user.email=nearproof@localhost commit -q -a -m "nearproof base patch"
  git -C "$U" apply "$P"
  git -C "$U" add -N .   # track new files so `git diff HEAD` reproduces the patch
fi
diff <(git -C "$U" diff HEAD -- crates | grep -v '^index ') <(grep -v '^index ' "$P") >/dev/null \
  || { echo "stark-backend-unified differs from patch" >&2; exit 1; }
echo "unified backend OK: $U"
