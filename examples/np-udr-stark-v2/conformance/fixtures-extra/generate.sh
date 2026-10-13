#!/usr/bin/env bash
# Regenerate the extra D0a fixtures (README.md) from the public D0a fixtures, then check them.
#   ./generate.sh [ROOT]     (default: this directory; ROOT/d0 and ROOT/mutants are replaced)
# Every case must be accepted by the independent Python reference (the generator's fixed point)
# and by the proved Lean `checkD0a B0` (`nearspec-v3-check-d0a`, zk-formal); `check.sh` re-runs
# both checkers and the D0a difftest.
set -eu
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../../.." && pwd)"
F="$repo/oracle/fixtures/v3/public-d0a/d0"
root="${1:-$here}"; out="$root/d0"; m="$root/mutants"
export PYTHONDONTWRITEBYTECODE=1
g() { local name=$1; shift; python3 "$here/gen_extra_d0a.py" --out "$out/$name" "$@"; }
rm -rf "$out"; mkdir -p "$out"

# (a) repeated source keys, consistent metadata (public dup byte 1)
g x-dup2-older     --base "$F/00-h10007-s3" --dup 1:3=1:2 --note "2 copies, older source block (block 1); = dupkey_v3.py"
g x-dup2-b2        --base "$F/01-h10004-s0" --dup 0:2=0:1 --note "2 copies in B2 (block 0)"
g x-dup3-b2        --base "$F/01-h10004-s0" --dup 0:2=0:1 --dup 0:4=0:1 --note "3 copies in B2, non-adjacent slots"
g x-dup4-b2        --base "$F/01-h10004-s0" --dup 0:2=0:1 --dup 0:3=0:1 --dup 0:4=0:1 --note "4 copies in B2 (every non-own slot)"
g x-dup2-cross     --base "$F/01-h10010-s1" --dup 1:0=0:0 --note "2 copies across source blocks (B2 slot copied into block 1)"
g x-dup2-cross-rev --base "$F/01-h10010-s1" --dup 0:1=1:1 --note "2 copies across source blocks (block-1 slot copied into B2)"
g x-dup3x2-cross   --base "$F/01-h10010-s1" --dup 1:1=0:0 --dup 1:2=0:0 --dup 0:3=1:3 --note "two repeated keys: one 3 copies (B2 + 2 in block 1), one 2 copies (block 1 + B2)"
g x-dup3-older     --base "$F/01-h10010-s1" --dup 1:1=1:0 --dup 1:2=1:0 --note "3 copies in an older source block (block 1)"
g x-dup2-implicit  --base "$F/00-h10025-s2" --dup 1:1=1:0 --note "2 copies in B2 with an implicit block after it (scheduler seed changes)"

# (b) present-but-empty values (zero-length VPRE jobs): BufferedReceiptGroupsQueueData
g x-empty1         --base "$F/00-h10011-s1" --groups 0=empty --note "one empty groups-data value, one non-empty"
g x-empty3         --base "$F/00-h10012-s0" --groups 1=empty,2=empty,3=empty --note "three empty groups-data values (equal value records)"
g x-empty-new      --base "$F/00-h10004-s3" --buffered 1,2 --note "new BufferedReceiptIndices; two empty groups-data values; no receipts"
g x-empty-mix      --base "$F/01-h10008-s0" --buffered 0,1=absent,4=0102 --note "new indices: empty / proven-absent / 2-byte groups data; 7 receipts"
g x-empty-implicit --base "$F/00-h10023-s2" --groups 3=empty --note "empty groups data with an implicit block (implicit base_state re-recorded)"

# (c) combinations
g x-dup-empty-implicit --base "$F/00-h10025-s2" --groups 3=empty --dup 1:1=1:0 --note "dup in B2 + empty value + implicit block"
g x-dup3-empty         --base "$F/01-h10024-s1" --groups 3=empty --dup 0:2=0:0 --dup 1:1=0:0 --note "3 copies across blocks + empty value"
g x-dup-empty-new      --base "$F/01-h10010-s1" --buffered 0,1,2 --dup 1:0=0:0 --note "cross-block dup + three empty values (new indices)"

# (d) claim-level negatives (mutants/): the same duplicates without the extra unused entries
rm -rf "$m"; mkdir -p "$m"
gm() { local name=$1; shift; python3 "$here/gen_extra_d0a.py" --out "$m/$name" --drop-extra "$@"; }
gm x-dup2-b2-noextra     --base "$F/01-h10004-s0" --dup 0:2=0:1 --note "x-dup2-b2 without the extra entry: reject"
gm x-dup3x2-noextra      --base "$F/01-h10010-s1" --dup 1:1=0:0 --dup 1:2=0:0 --dup 0:3=1:3 --note "x-dup3x2-cross without the 3 extra entries: reject"
gm x-dup-empty-noextra   --base "$F/00-h10025-s2" --groups 3=empty --dup 1:1=1:0 --note "x-dup-empty-implicit without the extra entry: reject"
