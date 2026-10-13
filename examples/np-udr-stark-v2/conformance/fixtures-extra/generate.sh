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

# (e) bandwidth requests: the scheduler's bucket shuffles draw ChaCha20 words (tables 8 chacha,
#     9 rng with the A9 word counter, 10 shuf).  A chunk header is edited where it is new and in
#     its copies in newer blocks (missed slots repeat it); BLK:* = the slots new in block BLK.
A=ffffffffff
g x-bw-pair          --base "$F/00-h10004-s3" --bw 0:0=2/0100000000 --bw 0:2=2/8000000000 --bw 0:3=2/0f00000000 --note "three requests to one receiver, one shuffle: 1 word"
g x-bw-16            --base "$F/00-h10004-s3" --bw 0:0=0/0f00000000,2/8000000000 --bw 0:2=0/8000000000,2/5555555555,3/ff00000000 --bw 0:3=1/5555555555,2/8000000000 --note "16 words: exactly one ChaCha20 block"
g x-bw-64            --base "$F/00-h10004-s3" --bw 0:0=0/5555555555,1/00000000ff --bw 0:2=1/5555555555,2/ffffffffff,3/ffffffffff --bw 0:3=3/8000000000 --note "64 words: exactly four ChaCha20 blocks"
g x-bw-65            --base "$F/00-h10004-s3" --bw 0:0=0/5555555555,1/ff00000000,3/ff00000000 --bw 0:2=2/ffffffffff --bw 0:3=0/5555555555,2/5555555555,3/ff00000000 --note "65 words: one word into a fifth ChaCha20 block"
g x-bw-all           --base "$F/00-h10004-s3" --bw "0:*=*/$A" --note "every new slot (3; slot 1 is missed) requests every shard, all 40 bits: 12 requests, 156 words"
g x-bw-implicit      --base "$F/00-h10024-s0" --bw "1:*=*/$A" --bw "0:*=*/$A" --note "all new slots of B2 and of the implicit block request every shard; 5 receipts: 195 + 160 words"
g x-bw-implicit-only --base "$F/00-h10024-s0" --bw "0:*=*/$A" --note "requests only in the implicit block's new chunks: 0 + 158 words"
g x-bw-n5            --base "$F/01-h10009-s1" --bw "1:*=*/$A" --bw "0:*=*/$A" --note "n=5, 25 + 20 requests (A8-maximal per new slot), main + implicit: 329 + 268 words"
g x-bw-noprior       --base "$F/00-h10024-s0" --state del:0f --bw "1:*=*/$A" --bw "0:*=*/$A" --note "no prior scheduler state (State.initial; ups BI) + all requests, main + implicit: 195 + 190 words"

# (f) scheduler upsert of key 0x0f (the ups table): every terminal case of traceUpsert
#     (Render/Ups/TreeTrace.lean) and every part kind, by main pre-state surgery (trie_edit.py;
#     canonical memory_usage).  Comment: main run [implicit run], terminal[parts bottom-up].
A72=$(printf '00%.0s' $(seq 72))
g x-ups-bi      --base "$F/00-h10024-s0" --state del:0f --note "BI[NLF,RBI,RDB] (0x0f absent, branch at [0]); implicit LP"
g x-ups-bi-ext  --base "$F/00-h10004-s3" --state del:0f --note "BI[NLF,RBI,RDE] (root extension [0])"
g x-ups-br      --base "$F/00-h10024-s0" --state put:0f01=00 --note "BR[RBR,RDB,RDB] (0x0f value in a branch); implicit BR"
g x-ups-bv      --base "$F/00-h10024-s0" --state put:0f01=00 --state put:0f11=00 --state del:0f --note "BV[RBV,RDB,RDB] (valueless branch at [0,15]); implicit BR"
g x-ups-lsa     --base "$F/00-h10004-s3" --state keep: --state put:=00 --note "LSa[NLF,SPB] (the only key is the empty key, a root leaf)"
g x-ups-lsb     --base "$F/00-h10024-s0" --state put:0f01=00 --state del:0f --note "LSb[MVL,SPB,RDB,RDB] (leaf 0x0f01 below slot 15); implicit BR"
g x-ups-lsc     --base "$F/00-h10004-s3" --state keep: --state put:0073326130=$A72 --state put:100000000000000000=00 --note "LSc[MVL,NLF,SPB,RDB] (one key under nibble 0)"
g x-ups-lsc-wex --base "$F/00-h10004-s3" --state keep: --state put:0073326130=$A72 --note "LSc[MVL,NLF,SPB,WEX] (single-leaf trie)"
g x-ups-esl0    --base "$F/00-h10024-s0" --state put:0f0101=00 --state put:0f0102=00 --state del:0f --note "ESl0[MVE,SPB,RDB,RDB] (extension [0,1,0] below slot 15); implicit BR"
g x-ups-esl1    --base "$F/00-h10024-s0" --state put:0f01=00 --state put:0f02=00 --state del:0f --note "ESl1[SPB,RDB,RDB] (extension [0] below slot 15); implicit BR"
g x-ups-esn0    --base "$F/00-h10024-s0" --state keep:00 --note "ESn0[MVE,NLF,SPB,WEX] (accounts only: root extension [0,0,7,3,...]); 5 receipts; implicit LP"
g x-ups-esn1    --base "$F/00-h10024-s0" --state keep:00 --state put:0061=@007332613030 --note "ESn1[NLF,SPB,WEX] (accounts only, two first id nibbles: root extension [0,0]); implicit LP"
g x-ups-pt      --base "$F/00-h10024-s0" --state ext0:0f --note "LP[RLP,PT,RDB,RDB] (non-canonical empty-key extension above the 0x0f leaf); implicit the same"

# (d) claim-level negatives (mutants/): the same duplicates without the extra unused entries
rm -rf "$m"; mkdir -p "$m"
gm() { local name=$1; shift; python3 "$here/gen_extra_d0a.py" --out "$m/$name" --drop-extra "$@"; }
gm x-dup2-b2-noextra     --base "$F/01-h10004-s0" --dup 0:2=0:1 --note "x-dup2-b2 without the extra entry: reject"
gm x-dup3x2-noextra      --base "$F/01-h10010-s1" --dup 1:1=0:0 --dup 1:2=0:0 --dup 0:3=1:3 --note "x-dup3x2-cross without the 3 extra entries: reject"
gm x-dup-empty-noextra   --base "$F/00-h10025-s2" --groups 3=empty --dup 1:1=1:0 --note "x-dup-empty-implicit without the extra entry: reject"
