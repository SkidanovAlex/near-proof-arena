#!/usr/bin/env bash
# Build oracle/fixtures/v3/arena-public-d0a: the public fixtures of `near-chunk-validation-d0-stark`
# (domain D0a, spec/near-chunk-validation-v0a.md) in the arena layout read by runners/worker
# NearV3Oracle:
#   cases/<n>/{request,witness,expected_claim}.bin + meta.json     positives (RelD0a holds)
#   rejections/<n>/{request,witness}.bin + meta.json              RelD0a false
#   params.bin                                                    near-arena-params-v3, domain D0a
#                                                                 (= NpUdrStarkV2.publicBin, 100 B)
# Sources (no regeneration; claim/witness bytes copied verbatim):
#   * oracle/fixtures/v3/arena-public (the D0 public set, 78 positives / 121 rejections), verbatim.
#     Every positive is in D0a (Lean nearspec-v3-check-d0a and oracle/tools/spec_check_v3_d0a.py:
#     78/78 accept, docs/logs/v3-d0a-challenge-2026-10.md); every rejection is false for RelD0
#     (nearcore rejects, or the honest chunk is outside D0), hence for RelD0a ⊆ RelD0.
#   * oracle/fixtures/v3/public-d0a/mutants (the D0a difftest set, oracle/v3-d0a): the first two
#     (by name) of each amendment family, so the public set exercises every D0a-only boundary:
#       positives  w.path_depth_at_bound    (A10 at Dp0 = 32; nearcore accepts, in D0a)
#       rejections w.path_depth_over        (A10, 33 items; nearcore accepts, outside D0a)
#                  w.foreign_routed_receipt (A2; Rel holds by construction, outside D0a)
#                  c.dup_bw_request         (A8; Rel holds by construction, outside D0a)
#                  w.empty_pre_state        (all-zero main pre-state root: not in RelD0, spec v0a §1)
#     each taken only if its meta.json agrees (expected_rel_d0a true for a positive, false for a
#     rejection).
#   spec/tools/build_public_d0a_arena.sh [OUT]
set -euo pipefail
repo="$(cd "$(dirname "$0")/../.." && pwd)"
out="${1:-$repo/oracle/fixtures/v3/arena-public-d0a}"
rm -rf "$out"; mkdir -p "$out"
python3 - "$repo" "$out" <<'PY'
import json, os, shutil, sys
repo, out = sys.argv[1:3]
src = os.path.join(repo, "oracle/fixtures/v3/arena-public")
d0a = os.path.join(repo, "oracle/fixtures/v3/public-d0a/mutants")
for sub in ("cases", "rejections"):
    shutil.copytree(os.path.join(src, sub), os.path.join(out, sub))
POS = ["w.path_depth_at_bound"]
NEG = ["w.path_depth_over", "w.foreign_routed_receipt", "c.dup_bw_request", "w.empty_pre_state"]
added = {}
for fam in POS + NEG:
    names = sorted(n for n in os.listdir(d0a) if n.endswith("-" + fam))[:2]
    if not names:
        sys.exit(f"no public-d0a mutant of family {fam}")
    for n in names:
        s = os.path.join(d0a, n)
        meta = json.load(open(os.path.join(s, "meta.json")))
        pos = fam in POS
        if meta.get("expected_rel_d0a") is not pos:
            sys.exit(f"{n}: expected_rel_d0a = {meta.get('expected_rel_d0a')}, wanted {pos}")
        dst = os.path.join(out, "cases" if pos else "rejections", n)
        if os.path.exists(dst):
            sys.exit(f"{n}: name collision with arena-public")
        os.makedirs(dst)
        shutil.copyfile(os.path.join(s, "claim.bin"), os.path.join(dst, "request.bin"))
        if pos:
            shutil.copyfile(os.path.join(s, "claim.bin"), os.path.join(dst, "expected_claim.bin"))
        shutil.copyfile(os.path.join(s, "witness.bin"), os.path.join(dst, "witness.bin"))
        shutil.copyfile(os.path.join(s, "meta.json"), os.path.join(dst, "meta.json"))
        added.setdefault(fam, []).append(n)
s = {"challenge": "near-chunk-validation-d0-stark", "domain": "D0a",
     "layout": "cases/<n>/{request,witness,expected_claim}.bin + meta.json; rejections/<n>/{request,witness}.bin + meta.json; params.bin (domain D0a)",
     "sources": {"arena-public": "oracle/fixtures/v3/arena-public (verbatim)",
                 "public-d0a": {"dir": "oracle/fixtures/v3/public-d0a/mutants", "positives": POS,
                                "rejections": NEG, "added": added}},
     "positives": len(os.listdir(os.path.join(out, "cases"))),
     "rejections": len(os.listdir(os.path.join(out, "rejections")))}
json.dump(s, open(os.path.join(out, "summary.json"), "w"), indent=1, sort_keys=True)
print(s["positives"], "positives,", s["rejections"], "rejections")
PY
python3 "$repo/spec/tools/params_bin_v3.py" "$out/params.bin" D0a >/dev/null
