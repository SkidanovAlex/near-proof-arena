# run-v2.d/rcptfam.sh — receipt-side tables from a real claim + witness, Rust vs Lean (sourced by
# run-v2.sh / run-v2-section.sh rcptfam; in scope: here src out npudr lr le le3 lp fx HEAVY pass bad).
#
# Ground truth: `np-lean-rcptfam-v3 <case> <dir>` (RcptFamV3.lean) evaluates the definitions of the
# accepted receipt-side renders (`AcceptedV3.rcptInput` and its list view + routing intervals,
# `accts`, `akeys`, `bnds`, `ddBlocks`/`ddRep`, `mrkLevels m.result.outcomes`,
# `NativeSortIds.sorted`) and the receipt SHA family on a real fixture, plus the first
# `planned + 8` rows of table 16 (`rcptTraceAlignedQ`; only when planned rows <= RCPTFAM_MAXROWS,
# default 4000: every Lean cell walks the plan, so the three fixtures with ~500-800 receipts skip
# table 16's rows, its view and table 19).  `npudr v3rcptfam` computes the same from the claim +
# witness alone (`src/v3/rcptfam.rs`).  Checks per case:
#   1. every entry list, the rcpt view (all RcptE fields + iv), the receipt SHA family and the
#      table-16 prefix rows are identical;
#   2. `npudr v3check` accepts the Rust table 16 (every constraint, honest publics, compact height);
#   3. the collector with `--native` (receipt side from claim + witness, trie/scheduler entries
#      from np-lean-shabins-v3) reproduces all four families, both bins and the cap of
#      np-lean-shabins-v3, and its bus check passes;
#   4. (first RCPTFAM_RENDER cases, default 3) the Rust entries rendered by Lean
#      (np-lean-render-v3-rcs: acct srcp mrk sort; np-lean-render-v3: akey bnd) and by
#      `npudr v3render` are byte-identical, and so for the first RCPTFAM_RENDER_EXTRA (2) extra
#      fixtures (a repeated source key: srcp dup rows, gated RC digests).
# Fixtures: public-d0a/d0 (64) and fixtures-extra/d0 (repeated source keys, empty values; lane
# v3-prover-fixtures).  Negatives: the fixtures-extra mutants are rejected by Lean `checkD0a`;
# a truncated witness is rejected by `npudr v3rcptfam`; tampered Rust entries (acct post byte,
# rcpt peoh / deposit byte, srcp leaf byte, mrk node byte) fail the collector's bus check; a
# tampered rcpt account byte (`bef`, carried by the MEM bus, not SHA) is caught by the differential.
# Lean dumps are cached in $out/rcptfam/<case>.lean (RCPTFAM_FRESH=1 to recompute).
rfd="$out/rcptfam"; mkdir -p "$rfd"
lrf="$here/.lake/build/bin/np-lean-rcptfam-v3"
lrr="$here/.lake/build/bin/np-lean-render-v3-rcs"
lsb="$here/.lake/build/bin/np-lean-shabins-v3"
air="$out/nearAirV3.json"
fxx="$here/fixtures-extra"
echo "== receipt-side entries from claim + witness: npudr v3rcptfam vs np-lean-rcptfam-v3"
cat > "$rfd/cmp.py" <<'PY'
import json, sys, os
L, R = sys.argv[1], sys.argv[2]
ld = lambda d, f: json.load(open(os.path.join(d, f)))
res = {}; why = {}
def first_diff(a, b, path=''):
    if type(a) != type(b): return f'{path}: {str(a)[:60]} vs {str(b)[:60]}'
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if a.get(k) != b.get(k): return first_diff(a.get(k), b.get(k), path + '.' + k)
    if isinstance(a, list):
        if len(a) != len(b): return f'{path}: len {len(a)} vs {len(b)}'
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y: return first_diff(x, y, f'{path}[{i}]')
    return f'{path}: {str(a)[:60]} vs {str(b)[:60]}'
def eq(name, a, b):
    res[name] = a == b
    if a != b: why[name] = first_diff(a, b)
for t in ('acct', 'akey', 'srcp', 'sort'):
    eq(t, ld(L, t + '.json'), ld(R, t + '.json'))
lm, rm = ld(L, 'mrk.json'), ld(R, 'mrk.json')
eq('mrk', (lm['n'], lm['levels']), (rm['n'], rm.get('levels', [])))
key = lambda ms: [(m['id'], list(m['bytes']), bool(m['dmult'])) for m in ms]
eq('sha_receipt', key(ld(L, 'sha_receipt.json')), key(ld(R, 'sha_receipt.json')))
s = ld(L, 'summary.json')
if s['traced']:
    eq('rcpt', ld(L, 'rcpt.json'), ld(R, 'rcpt.json'))
    eq('bnd', ld(L, 'bnd.json'), ld(R, 'bnd.json'))
    res['prefix'] = open(os.path.join(L, 'rcpt.prefix.bin'), 'rb').read() == \
        open(os.path.join(R, 'rcpt.prefix.bin'), 'rb').read()
ok = all(res.values())
print(' '.join(k for k, v in res.items() if v), '|',
      f"{s['receipts']} receipts, {s['lists']} lists, {s['rows']} rows, {s['accts']} accts" +
      ('' if s['traced'] else ' (untraced: rcpt/bnd/prefix not compared)'), '|',
      ' ; '.join(f'{k}: {why.get(k)}' for k, v in res.items() if not v))
sys.exit(0 if ok else 1)
PY
cat > "$rfd/bins.py" <<'PY'
import json, sys
L = json.load(open(sys.argv[1])); R = json.load(open(sys.argv[2]))
key = lambda ms: [(m['id'], list(m['bytes']), bool(m['dmult'])) for m in ms]
ok = {f: key(L[f]) == key(R[f]) for f in ('scheduler', 'native', 'receipt', 'source', 'b0', 'b1')}
ok['cap'] = L['cap'] == R['cap']
b = R['bus']
ok['bus'] = not b['bad_recvs'] and not b['bad_sends'] and b['unsent'] == 0
print(' '.join(k for k, v in ok.items() if v), '|', f"receipt {len(L['receipt'])} jobs, bus {b['sends']} sends / {b['recvs']} recvs",
      '|', ' '.join(k for k, v in ok.items() if not v))
sys.exit(0 if all(ok.values()) else 1)
PY
nrf=0; nrfail=0; nrend=0; nuntr=0
rf_case() { # rf_case <label> <case_dir>
  local c="$1" d="$2" ld="$rfd/$1.lean" rd="$rfd/$1.rust" ed="$rfd/$1.ent" res t
  if [ -n "${RCPTFAM_FRESH:-}" ] || [ ! -s "$ld/summary.json" ]; then
    rm -rf "$ld"
    if ! $HEAVY "$lrf" "$d" "$ld" "${RCPTFAM_MAXROWS:-4000}" >"$rfd/$c.lean.log" 2>&1; then
      bad "$c: np-lean-rcptfam-v3 failed"; tail -2 "$rfd/$c.lean.log"; nrfail=$((nrfail+1)); return; fi
  fi
  rm -rf "$rd"
  if ! "$npudr" v3rcptfam "$d/claim.bin" "$d/witness.bin" "$rd" >"$rfd/$c.rust.log" 2>&1; then
    bad "$c: npudr v3rcptfam failed"; tail -2 "$rfd/$c.rust.log"; nrfail=$((nrfail+1)); return; fi
  if res=$(python3 "$rfd/cmp.py" "$ld" "$rd"); then pass "$c: identical [${res%%|*}] (${res#*| })"
  else bad "$c: differs (${res##*| })"; nrfail=$((nrfail+1)); fi
  case "$res" in *untraced*) nuntr=$((nuntr+1)) ;; esac
  if "$npudr" v3check "$air" rcpt "$rd/rcpt.json" >"$rd/rcpt.check" 2>&1; then
    pass "$c: rcpt (Rust, real witness) $(cut -c5- "$rd/rcpt.check")"
  else bad "$c: rcpt constraints fail"; head -3 "$rd/rcpt.check"; nrfail=$((nrfail+1)); fi
  # the collector, receipt side native
  if [ ! -s "$rfd/$c.shabins.json" ]; then
    $HEAVY "$lsb" "$d" > "$rfd/$c.shabins.json" 2>"$rfd/$c.shabins.err" || { bad "$c: np-lean-shabins-v3 failed"; nrfail=$((nrfail+1)); return; }
  fi
  rm -rf "$ed"; mkdir -p "$ed"
  python3 - "$rfd/$c.shabins.json" "$ed" <<'PY'
import json, sys, os
d = json.load(open(sys.argv[1]))
for t in ('node', 'val', 'ups', 'codec'):
    json.dump(d['entries'][t], open(os.path.join(sys.argv[2], t + '.json'), 'w'))
PY
  if "$npudr" v3sha "$ed" "$ed/t.json" "$ed/r.json" "$ed/full.json" --native "$d/claim.bin" "$d/witness.bin" 2>"$ed/err" \
     && res=$(python3 "$rfd/bins.py" "$rfd/$c.shabins.json" "$ed/full.json"); then
    pass "$c: collector --native == np-lean-shabins-v3 [${res%%|*}] (${res#*| })"
  else bad "$c: collector --native differs (${res##*| }) $(tail -1 "$ed/err")"; nrfail=$((nrfail+1)); fi
  if [ $nrend -lt "${RCPTFAM_RENDER:-3}" ]; then
    nrend=$((nrend+1))
    for t in acct srcp mrk sort akey bnd; do
      [ -s "$rd/$t.json" ] || continue
      if [ $t = akey ] || [ $t = bnd ]; then $HEAVY "$lr" $t "$rd/$t.json" "$rd/$t.lean.bin" 2>"$rd/$t.err"
      else $HEAVY "$lrr" $t "$rd/$t.json" "$rd/$t.lean.bin" 2>"$rd/$t.err"; fi || { bad "$c $t: Lean render failed"; continue; }
      "$npudr" v3render $t "$rd/$t.json" "$rd/$t.rust.bin" || { bad "$c $t: npudr v3render failed"; continue; }
      if cmp -s "$rd/$t.lean.bin" "$rd/$t.rust.bin"; then
        pass "$c $t: render of the real entries identical (sha256 $(sha256sum "$rd/$t.rust.bin" | cut -c1-16))"
      else bad "$c $t: render differs"; nrfail=$((nrfail+1)); fi
      rm -f "$rd/$t.lean.bin" "$rd/$t.rust.bin"
    done
  fi
  nrf=$((nrf+1))
}
for case in $(ls "$fx" | head -${RCPTFAM_CASES:-1000}); do
  [ -f "$fx/$case/witness.bin" ] && rf_case "$case" "$fx/$case"
done
if [ -d "$fxx/d0" ]; then
  nrend=$(( ${RCPTFAM_RENDER:-3} - ${RCPTFAM_RENDER_EXTRA:-2} ))   # also render the first extra cases
  for case in $(ls "$fxx/d0"); do
    [ -f "$fxx/d0/$case/witness.bin" ] && rf_case "$case" "$fxx/d0/$case"
  done
else bad "fixtures-extra/d0 missing"; fi
echo "   ($nrf fixtures, $nuntr untraced; $nrfail failures)"

echo "== receipt-side negatives"
if [ -d "$fxx/mutants" ]; then
  for m in $(ls "$fxx/mutants"); do
    if $HEAVY "$lrf" "$fxx/mutants/$m" "$rfd/neg-$m" >"$rfd/neg-$m.log" 2>&1; then bad "mutant $m: Lean accepted"
    else pass "mutant $m: checkD0a rejects ($(grep -o 'checkD0a failed: .*' "$rfd/neg-$m.log" | cut -c1-70))"; fi
  done
fi
c0=$(ls "$fx" | head -1); d0="$fx/$c0"
head -c $(( $(stat -c %s "$d0/witness.bin") - 1 )) "$d0/witness.bin" > "$rfd/neg-trunc.witness"
if "$npudr" v3rcptfam "$d0/claim.bin" "$rfd/neg-trunc.witness" "$rfd/neg-trunc" >"$rfd/neg-trunc.log" 2>&1; then
  bad "$c0 truncated witness: v3rcptfam accepted"
else pass "$c0 truncated witness: v3rcptfam rejects ($(tail -1 "$rfd/neg-trunc.log" | cut -c1-60))"; fi
# tampered entries: pick a fixture with receipts on both sides of the receipt family
cn=""; for c in $(ls "$fx"); do
  [ -s "$rfd/$c.rust/rcpt.json" ] && [ -d "$rfd/$c.ent" ] || continue
  python3 -c "import json,sys; r=json.load(open('$rfd/$c.rust/rcpt.json')); sys.exit(0 if sum(len(l['rs']) for l in r['lists'])>=2 else 1)" && { cn=$c; break; }
done
if [ -n "$cn" ]; then
  for mut in acct-post rcpt-peoh rcpt-dep srcp-leaf mrk-node rcpt-bef; do
    nd="$rfd/neg-$cn-$mut"; rm -rf "$nd"; cp -r "$rfd/$cn.ent" "$nd"; rm -f "$nd"/{t,r,full}.json
    for t in rcpt acct srcp mrk; do cp "$rfd/$cn.rust/$t.json" "$nd/"; done
    python3 - "$nd" "$mut" <<'PY'
import json, sys, os
d, m = sys.argv[1:]
ld = lambda t: json.load(open(os.path.join(d, t + '.json'))); sv = lambda t, v: json.dump(v, open(os.path.join(d, t + '.json'), 'w'))
if m == 'acct-post': a = ld('acct'); a[0]['post'][0] ^= 1; sv('acct', a)
elif m.startswith('rcpt-'):
    r = ld('rcpt'); x = next(x for l in r['lists'] for x in l['rs']); f = m[5:]; x[f][0] = (x[f][0] + 1) % 256; sv('rcpt', r)
elif m == 'srcp-leaf': b = ld('srcp'); next(B for B in b if not B['dup'])['leaf'][0] ^= 1; sv('srcp', b)
elif m == 'mrk-node':
    v = ld('mrk'); nd = next(n for n in v['nodes'] if 'hashed' in n); nd['hashed']['l'][0] ^= 1; sv('mrk', v)
PY
    if [ $mut = rcpt-bef ]; then
      if cmp -s <(python3 -c "import json;print(json.dumps(json.load(open('$nd/rcpt.json')),sort_keys=True))") \
                <(python3 -c "import json;print(json.dumps(json.load(open('$rfd/$cn.lean/rcpt.json')),sort_keys=True))"); then
        bad "$cn neg $mut: differential misses it"
      else pass "$cn neg $mut: differs from the Lean view (MEM-bus field, not on the SHA buses)"; fi
      continue
    fi
    if "$npudr" v3sha "$nd" "$nd/t.json" "$nd/r.json" 2>"$nd/err"; then bad "$cn neg $mut: bus check still passes"
    else pass "$cn neg $mut: bus check rejects ($(grep -o '[0-9]* sends ([0-9]* unmatched), [0-9]* receives ([0-9]* unmatched)' "$nd/err"))"; fi
  done
else bad "rcptfam negatives: no fixture with >= 2 receipts"; fi
