# shellcheck shell=bash
# run-v2.d/prove.sh — the END-TO-END v3 proof of a real D0a fixture, checked by the deployed Lean
# verifier (sourced by run-v2.sh / run-v2-section.sh prove; in scope: here src out npudr fx HEAVY
# pass bad).  GATED: runs only with PROVE_V3=1 (each proof commits 25 tables, six of them at the
# fixed 2^22 rows: minutes of CPU and ~20 GB; run it under HEAVY_MEM=32G, alone).
#
# Per case (PROVE_CASES, default the smallest public D0a fixture 00-h10004-s3):
#   1. differential of the scheduler/ChaCha/qv entries: `np-lean-bundle-v3 <case> <x>`
#      (BundleV3.lean, the completeness proof's `PriorCore` blocks evaluated in Lean) ==
#      `npudr v3sched <case> <r>` (native Rust, lane v3-prover-schedqv) for sched (11–15),
#      chacha/rng/shuf (8–10) and qv (22);
#   2. `npudr v3prove <case> <p>`: everything from claim + witness in Rust — hint (`hintOf`),
#      prepared statement (`prepD0` + `Public.preparedBytes · 0`), all 25 tables (v3trie,
#      v3sched, v3rcptfam, SHA collector), every table's constraints, EVERY bus balanced
#      (tables + public messages),
#      the STARK at auxGroup 2 over (public.bin, prepared), proof = `join (Hint.encode h) π`;
#      the Rust verifier re-checks π;
#   3. `np-lean-verify-v3 public.bin claim.bin proof.bin` — the deployed model
#      `(npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier.deployed` — accepts;
#   4. proof size ≤ challenge cap 8 MiB (`maxProofBytes`, `challengeParamsD0a`);
#   5. negatives, each must be rejected by the Lean verifier: STARK byte flips (first byte of π,
#      middle, last), truncated / extended proof, empty proof, hint `n` byte flip, hint body byte flip (offset 12 = first body byte), outer hint length
#      prefix +1, wrong public tape, claim byte flips (header, middle, last), another fixture's
#      claim with this proof.
# Knobs: PROVE_CASES (dirs), PROVE_NEG (1: run step 5), PROVE_REUSE (1: keep an existing proof), NPUDR_MEM_GB (prover budget, default 20).
if [ "${PROVE_V3:-0}" != 1 ]; then
  echo "== v3 end-to-end proof: skipped (set PROVE_V3=1; heavy, run alone under HEAVY_MEM=32G)"
else
pd="$out/prove"; mkdir -p "$pd"
lb="$here/.lake/build/bin/np-lean-bundle-v3"
lv3="$here/.lake/build/bin/np-lean-verify-v3"
air="$out/nearAirV3.json"
# the D0a public tape: formal/NpUdrStarkV2/PublicBin.lean `publicBin` (sha256 ab13c199…957f)
python3 - "$here/../formal/NpUdrStarkV2/PublicBin.lean" "$pd/public.bin" <<'PY'
import re, sys, hashlib
s = open(sys.argv[1]).read(); body = s[s.index('def publicBin'):]
body = body[body.index('[') + 1:body.index(']')]
b = bytes(int(x, 16) for x in re.findall(r'0x[0-9a-fA-F]+', body))
assert hashlib.sha256(b).hexdigest().startswith('ab13c199'), 'publicBin digest drift'
open(sys.argv[2], 'wb').write(b)
PY
# mut <in> <out> <op> [<arg>]: byte-level mutations
mut() {
  python3 - "$@" <<'PY'
import sys
src, dst, op = sys.argv[1], sys.argv[2], sys.argv[3]
b = bytearray(open(src, 'rb').read())
a = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] else 0
if op == 'flip': b[a % len(b)] ^= 1
elif op == 'trunc': b = b[:len(b) - max(a, 1)]
elif op == 'ext': b += b'\0'
elif op == 'empty': b = bytearray()
elif op == 'lenplus':  # borsh u32 length prefix + 1
  n = int.from_bytes(b[0:4], 'little') + 1; b[0:4] = n.to_bytes(4, 'little')
open(dst, 'wb').write(bytes(b))
PY
}
lver() { $HEAVY "$lv3" "$1" "$2" "$3" > "$4.out" 2> "$4.err"; }
for d in ${PROVE_CASES:-$fx/00-h10004-s3}; do
  case=$(basename "$d"); x="$pd/$case.extra"; p="$pd/$case"
  t0=$(date +%s)
  if [ "${PROVE_REUSE:-0}" = 1 ] && [ -s "$p/proof.bin" ]; then
    echo "  $case: PROVE_REUSE=1, reusing $p/proof.bin ($(grep '^proof' "$p.log" 2>/dev/null))"
  else
  rm -rf "$x" "$p" "$p.sched" "$p.neg"; mkdir -p "$x" "$p"
  if ! $HEAVY "$lb" "$d" "$x" > "$x.log" 2>&1; then bad "$case: np-lean-bundle-v3 failed ($(tail -c 300 "$x.log"))"; continue; fi
  if ! "$npudr" v3sched "$d" "$p.sched" > "$p.sched.log" 2>&1; then bad "$case: npudr v3sched failed ($(tail -c 300 "$p.sched.log"))"; continue; fi
  if python3 - "$x" "$p.sched" <<'PY'
import json, sys
L, R = sys.argv[1], sys.argv[2]
ld = lambda f: json.load(open(f))
bad = [t for t, lf in [("sched", "sched.json"), ("chacha", "chacha.json"), ("rng", "rng.json"),
                       ("shuf", "shuf.json"), ("qv", "qv.json")]
       if ld(f"{L}/{lf}") != ld(f"{R}/{'codec.json' if t == 'sched' else lf}")]
print(" ".join(bad)); sys.exit(1 if bad else 0)
PY
  then pass "$case: tables 8-15, 22 entries: Lean (np-lean-bundle-v3) == Rust (npudr v3sched) ($(cat "$x.log"))"
  else bad "$case: Lean vs Rust scheduler/qv entries differ"; fi
  if ! NPUDR_MEM_GB=${NPUDR_MEM_GB:-20} /usr/bin/time -f "%e s, max RSS %M KB" $HEAVY "$npudr" v3prove "$d" "$p" \
      --air "$air" --pub "$pd/public.bin" > "$p.log" 2>&1; then
    bad "$case: npudr v3prove failed ($(grep -E 'IMBALANCE|FAIL|error|v3prove:' "$p.log" | head -5))"; continue
  fi
  pass "$case: v3prove: 25 tables, constraints hold, $(grep -c 'balanced$' "$p.log") buses balanced; $(grep '^proof' "$p.log"); $(tail -1 "$p.log")"
  fi
  sz=$(stat -c %s "$p/proof.bin")
  if [ "$sz" -le 8388608 ]; then pass "$case: proof $sz B <= maxProofBytes 8388608"; else bad "$case: proof $sz B > 8 MiB"; fi
  if lver "$pd/public.bin" "$p/claim.bin" "$p/proof.bin" "$p.lean" && grep -qx accept "$p.lean.out"; then
    pass "$case: np-lean-verify-v3 (deployed npVerifierP challengeSpecD0a nearAirV3 split prepV3b) ACCEPTS ($(cat "$p.lean.err"))"
  else
    bad "$case: np-lean-verify-v3 does not accept ($(cat "$p.lean.out" "$p.lean.err" | tr '\n' ' '))"; continue
  fi
  [ "${PROVE_NEG:-1}" = 1 ] || continue
  hl=$(python3 -c "import sys;b=open('$p/proof.bin','rb').read();print(int.from_bytes(b[0:4],'little'))")
  pi0=$((4 + hl)); mid=$(( (pi0 + sz) / 2 ))
  other=$(ls -d "$fx"/*/ | grep -v "/$case/" | head -1)
  negs="pi-first:proof:flip:$pi0 pi-mid:proof:flip:$mid pi-last:proof:flip:$((sz - 1)) trunc:proof:trunc:1 \
ext:proof:ext empty:proof:empty hint-n:proof:flip:4 hint-body:proof:flip:12 hint-len:proof:lenplus pub:pub:flip:5 \
claim-hdr:claim:flip:3 claim-mid:claim:flip:$(( $(stat -c %s "$p/claim.bin") / 2 )) claim-last:claim:flip:$(( $(stat -c %s "$p/claim.bin") - 1 )) other-claim:other"
  nrej=0; nneg=0
  for n in $negs; do
    IFS=: read -r name what op arg <<< "$n"
    pb="$p/proof.bin"; cb="$p/claim.bin"; ub="$pd/public.bin"; ng="$p.neg/$name"
    mkdir -p "$p.neg"
    case $what in
      proof) mut "$p/proof.bin" "$ng" "$op" "$arg"; pb="$ng" ;;
      claim) mut "$p/claim.bin" "$ng" "$op" "$arg"; cb="$ng" ;;
      pub) mut "$pd/public.bin" "$ng" "$op" "$arg"; ub="$ng" ;;
      other) cb="$other/claim.bin" ;;
    esac
    nneg=$((nneg + 1))
    lver "$ub" "$cb" "$pb" "$ng.lean"
    if grep -qx reject "$ng.lean.out"; then nrej=$((nrej + 1)); pass "$case: negative $name rejected"
    else bad "$case: negative $name NOT rejected ($(cat "$ng.lean.out" "$ng.lean.err" | tr '\n' ' '))"; fi
  done
  echo "  $case: $nrej/$nneg negatives rejected by the Lean verifier; $(( $(date +%s) - t0 )) s"
done
fi
