#!/bin/sh
# Generates gen/src: a copy of examples/np-udr-stark-v2/source/src with two env-gated FORGING
# hooks in prover.rs (and `pub mod forge;` in lib.rs). Nothing else changes; the verifier is
# checked byte-identical to the deployed one. Without NPUDR_FORGE / NPUDR_FORGE_BUS set the
# prover behaves exactly as the original (same code path).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../../../examples/np-udr-stark-v2/source/src"
rm -rf "$here/gen"; mkdir -p "$here/gen"
cp -r "$src" "$here/gen/src"
cp "$here/forge.rs" "$here/gen/src/forge.rs"
cp "$src/../near-air.json" "$src/../near-air-v3.json" "$here/gen/"
python3 - "$here/gen/src" <<'PY'
import sys
d = sys.argv[1]
p = d + "/lib.rs"; s = open(p).read(); s = s.replace("pub mod field;", "pub mod field;\npub mod forge;", 1); open(p, "w").write(s)
p = d + "/prover.rs"; s = open(p).read()
a = """        for a in &srcs {
            aux_finals.extend(a.finals());
        }
"""
assert s.count(a) == 1
s = s.replace(a, a + """        crate::forge::balance_finals(air, &mut aux_finals, cb, alpha_fp, gamma);
""")
b = """    global_checks(air, &sch, &ood, &aux_finals, &pre, &pubs, &pmsgs)
        .map_err(|e| format!("{e}: the trace does not satisfy the AIR"))?;
"""
assert s.count(b) == 1
s = s.replace(b, """    crate::forge::fix_ood(air, &sch, &mut ood, &aux_finals, &pre, &pubs);
    if crate::forge::mode() == 0 {
        global_checks(air, &sch, &ood, &aux_finals, &pre, &pubs, &pmsgs)
            .map_err(|e| format!("{e}: the trace does not satisfy the AIR"))?;
    }
""")
c = """        if *v != p0 + p1 * crate::protocol::point(l0, sch.fri_l, j) {"""
assert s.count(c) == 1
s = s.replace(c, """        if crate::forge::mode() == 0 && *v != p0 + p1 * crate::protocol::point(l0, sch.fri_l, j) {""")
open(p, "w").write(s)
PY
cmp "$src/verifier.rs" "$here/gen/src/verifier.rs"
echo "gen/src generated (verifier.rs identical to the deployed one)"
