#!/usr/bin/env bash
# lane/pq-stream-commit: regenerate the streamed-commitment overlay patches from a working deps
# tree (DEPS, default /data/illia/nearproof-deps/pq-stream) set up by setup_stream_deps.sh:
#   patches/stark-backend-stream.patch    on top of stark-backend-unified.patch
#   patches/openvm-recursion-stream.patch on top of openvm-recursion-sha384.patch
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-stream}
OUT=${STREAM_PATCH_OUT:-$HERE/patches}
T=$(mktemp -d "$DEPS/.mkpatch.XXXX")
trap 'rm -rf "$T"' EXIT
gitq() { git -C "$1" -c user.name=nearproof -c user.email=nearproof@localhost "${@:2}"; }

# backend: base (pinned + native patch) + unified patch, committed; overlay = diff to the live tree
cp -a "$DEPS/stark-backend" "$T/sb"; rm -rf "$T/sb/target"
gitq "$T/sb" commit -q -a -m base
gitq "$T/sb" apply "$HERE/patches/stark-backend-unified.patch"
gitq "$T/sb" add -A; gitq "$T/sb" commit -q -m unified
rsync -a --delete "$DEPS/stark-backend-unified/crates/" "$T/sb/crates/"
gitq "$T/sb" add -A
gitq "$T/sb" diff --cached HEAD -- crates | grep -v '^index ' > "$OUT/stark-backend-stream.patch"

# recursion crate: OpenVM rev + recursion patch, committed; overlay = diff to the live tree
mkdir "$T/ov"; cp -a "$DEPS/openvm-sha384/." "$T/ov/"
gitq "$T/ov" reset -q; gitq "$T/ov" checkout -q -- .; gitq "$T/ov" clean -qfdx
gitq "$T/ov" apply "$HERE/patches/openvm-recursion-sha384.patch" 2>/dev/null
gitq "$T/ov" add -A; gitq "$T/ov" commit -q -m recursion
rsync -a --delete --exclude target --exclude .git "$DEPS/openvm-sha384/" "$T/ov/"
gitq "$T/ov" add -A
gitq "$T/ov" diff --cached HEAD | grep -v '^index ' > "$OUT/openvm-recursion-stream.patch"
wc -l "$OUT/stark-backend-stream.patch" "$OUT/openvm-recursion-stream.patch"
