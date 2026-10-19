#!/usr/bin/env bash
# lane/pq-cpu-prover: regenerate the fast-CPU-prover overlay patches from a working deps tree
# (DEPS, default /data/illia/nearproof-deps/pq-cpu) set up by setup_cpu_fast_deps.sh:
#   patches/stark-backend-cpu-fast.patch  on top of stark-backend-unified.patch + stark-backend-stream.patch
#   patches/plonky3-ext12-simd.patch      on top of ../patches/plonky3-ext12.patch
#   patches/openvm-recursion-cpu-fast.patch on top of openvm-recursion-sha384.patch + openvm-recursion-stream.patch
#                                          (multi-buffer SHA-384; bench examples excluded)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-cpu2}
OUT=${CPU_FAST_PATCH_OUT:-$HERE/patches}
T=$(mktemp -d "$DEPS/.mkpatch.XXXX")
trap 'rm -rf "$T"' EXIT
gitq() { git -C "$1" -c user.name=nearproof -c user.email=nearproof@localhost "${@:2}"; }

# backend: base (pinned + native patch) + unified + stream, committed; overlay = diff to the live tree
cp -a "$DEPS/stark-backend" "$T/sb"; rm -rf "$T/sb/target"
gitq "$T/sb" commit -q -a -m base
gitq "$T/sb" apply "$HERE/patches/stark-backend-unified.patch"
gitq "$T/sb" apply "$HERE/patches/stark-backend-stream.patch"
gitq "$T/sb" add -A; gitq "$T/sb" commit -q -m unified+stream
rsync -a --delete "$DEPS/stark-backend-unified/crates/" "$T/sb/crates/"
gitq "$T/sb" add -A
gitq "$T/sb" diff --cached HEAD -- crates | grep -v '^index ' > "$OUT/stark-backend-cpu-fast.patch"

# plonky3: crates.io sources + the Ext12 patch; overlay = diff to the live tree
mkdir "$T/p3"; cp -a "$DEPS/plonky3-ext12/.orig/." "$T/p3/"
(cd "$T/p3" && patch -s -p1 < "$HERE/../patches/plonky3-ext12.patch")
(cd "$T" && for c in p3-baby-bear p3-monty-31; do diff -ruN "p3/$c" "$DEPS/plonky3-ext12/$c" | sed -e "s|^--- p3/|--- a/|" -e "s|^+++ $DEPS/plonky3-ext12/|+++ b/|" || true; done) \
  | grep -v "^diff -ruN" | sed -E "/^(---|\+\+\+) /s/\t.*$//" > "$OUT/plonky3-ext12-simd.patch"
# recursion crate: OpenVM rev + recursion + stream patches, committed; overlay = diff to the live tree
mkdir "$T/ov"; cp -a "$DEPS/openvm-sha384/." "$T/ov/"; rm -rf "$T/ov/target"
gitq "$T/ov" reset -q; gitq "$T/ov" checkout -q -- .; gitq "$T/ov" clean -qfdx
gitq "$T/ov" apply "$HERE/patches/openvm-recursion-sha384.patch" 2>/dev/null
gitq "$T/ov" apply "$HERE/patches/openvm-recursion-stream.patch"
gitq "$T/ov" add -A; gitq "$T/ov" commit -q -m recursion+stream
rsync -a --delete --exclude target --exclude .git --exclude crates/recursion/examples "$DEPS/openvm-sha384/" "$T/ov/"
gitq "$T/ov" add -A
gitq "$T/ov" diff --cached HEAD | grep -v '^index ' > "$OUT/openvm-recursion-cpu-fast.patch"
wc -l "$OUT/stark-backend-cpu-fast.patch" "$OUT/plonky3-ext12-simd.patch" "$OUT/openvm-recursion-cpu-fast.patch"
