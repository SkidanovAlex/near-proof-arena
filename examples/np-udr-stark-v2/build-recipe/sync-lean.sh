#!/usr/bin/env bash
# Packager step (NOT run by the judge; needs the repository checkout): compute
# the exact import closure of formal/NpUdrStarkV2/*.lean and vendor the sources
# the offline build compiles, pinning their digests in dependency-locks/.
#
#   source/lean-vendor/   JUDGE-TRUSTED packages (ArenaCore, NearSpec,
#                         NearSpecV3), verbatim at commit PIN. The judge
#                         supplies its own pinned copies; these exist only so
#                         build.sh can replicate its native-lean build offline.
#                         -> dependency-locks/lean-vendor.sha256
#   formal/ZkFormal/      CANDIDATE code: the zk-formal Lake package
#   formal/ReexecV3D0/    (and the reference candidate's witness normal form,
#                         which zk-formal's v3 modules import). Neither is in
#                         the challenge's trusted `allowed_packages`, so they
#                         cannot be a `require` nor live in lean-vendor: the
#                         judge stages only formal/, and a model module may
#                         import only trusted modules, other formal/ modules
#                         and Init (pipeline.rs `native_build`). They ship
#                         inside formal/ and are part of the model closure.
#                         -> dependency-locks/zk-formal.sha256
#
# The vendored candidate set is exactly the import closure of formal/NpUdrStarkV2/*.lean, so
# it follows the certificate's (pruned) closure: zk-formal modules the certificate does not use
# are not shipped and not elaborated by the judge (lane v3-prune, docs/logs/v3-prune-2026-10.md;
# `zk-formal/scripts/ClosureDeps.lean` reports which modules define constants the certificate
# needs, `zk-formal/scripts/judge-time.py` times the shipped closure judge-style).
#
# usage: build-recipe/sync-lean.sh   (from anywhere), PIN=<commit> (default HEAD)
set -euo pipefail
PIN="${PIN:-$(git -C "$(dirname "$0")" rev-parse HEAD)}"
pkg="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(git -C "$pkg" rev-parse --show-toplevel)"

# The trusted module roots: package name -> repo src_root.
#   ArenaCore    -> formal-core
#   NearSpec     -> spec/lean
#   NearSpecV3   -> spec/lean/v3
# (the challenge lists include-prefixes; the judge compiles the transitive
# trusted closure, so we vendor the whole reachable set, not just the prefixes).
rm -rf "$pkg/source/lean-vendor" "$pkg/formal/ZkFormal" "$pkg/formal/ZkFormal.lean" \
  "$pkg/formal/ReexecV3D0"
mkdir -p "$pkg/source/lean-vendor/formal-core" "$pkg/source/lean-vendor/spec/lean" \
  "$pkg/source/lean-vendor/spec/lean/v3"

python3 - "$repo" "$pkg" <<'PY'
import os, re, shutil, sys
repo, pkg = sys.argv[1], sys.argv[2]

# module root -> repo directory holding the .lean tree
ROOTS = [
    ("ArenaCore", "formal-core"),
    ("NearSpecV3", "spec/lean/v3"),
    ("NearSpec", "spec/lean"),
    ("ZkFormal", "zk-formal"),
    ("ReexecV3D0", "examples/reexec-v3-d0/formal"),
]
# trusted roots vendored into source/lean-vendor/<root>/...
TRUSTED = {"ArenaCore": "formal-core", "NearSpec": "spec/lean",
           "NearSpecV3": "spec/lean/v3"}
# candidate roots vendored into formal/<root>/...
CANDIDATE = {"ZkFormal": "ZkFormal", "ReexecV3D0": "ReexecV3D0"}

def source_of(mod):
    for root, d in ROOTS:
        if mod == root or mod.startswith(root + "."):
            p = os.path.join(repo, d, *mod.split(".")) + ".lean"
            if os.path.isfile(p):
                return root, p
    return None, None

def local(mod):
    # the candidate's own package, or a judge-generated module: already staged
    # (NpUdrStarkV2/*.lean) or supplied by the judge (ArenaExpectedInst).
    return mod == "NpUdrStarkV2" or mod.startswith("NpUdrStarkV2.") or mod == "ArenaExpectedInst"

def imports(path):
    txt = open(path, encoding="utf-8").read()
    txt = re.sub(r"/-.*?-/", "", txt, flags=re.S)
    txt = re.sub(r"--[^\n]*", "", txt)
    return re.findall(r"^\s*import\s+([A-Za-z0-9_.']+)", txt, flags=re.M)

seeds = []
here = os.path.join(pkg, "formal", "NpUdrStarkV2")
for f in sorted(os.listdir(here)):
    if f.endswith(".lean"):
        seeds += imports(os.path.join(here, f))

seen, missing, trusted_mods, cand_mods = set(), set(), {}, {}
todo = list(seeds)
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen.add(m)
    root, p = source_of(m)
    if p is None:
        if m.split(".")[0] in ("Init", "Std", "Lean") or local(m):
            continue
        missing.add(m)
        continue
    if root in TRUSTED:
        trusted_mods[m] = p
    elif root in CANDIDATE:
        cand_mods[m] = p
    else:
        sys.exit(f"sync-lean: closure imports {m} from unknown root {root}")
    todo += imports(p)

if missing:
    sys.exit("sync-lean: closure imports non-trusted/non-toolchain modules: "
             + ", ".join(sorted(missing)))

# copy trusted modules
for m, p in trusted_mods.items():
    root = next(r for r in TRUSTED if m == r or m.startswith(r + "."))
    rel = os.path.join(TRUSTED[root], *m.split(".")) + ".lean"
    dst = os.path.join(pkg, "source", "lean-vendor", rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copyfile(p, dst)
# copy candidate modules
for m, p in cand_mods.items():
    root = next(r for r in CANDIDATE if m == r or m.startswith(r + "."))
    # formal/<module path>.lean: the judge names a staged module by its path under formal/
    # (staging.rs) and build.sh copies formal/${m//.//}.lean (was formal/<root>/<module path>,
    # i.e. ZkFormal/ZkFormal/..., which neither resolves).
    rel = os.path.join(*m.split(".")) + ".lean"
    dst = os.path.join(pkg, "formal", rel)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copyfile(p, dst)

for label, n, trusted in (("trusted", len(trusted_mods), True),
                          ("candidate", len(cand_mods), False)):
    print(f"sync-lean: {label} closure: {n} modules")
PY

# Lakefiles for the vendored trusted packages (the judge computes its own build
# plan; these exist for local `lake build` parity).
cat > "$pkg/source/lean-vendor/formal-core/lakefile.toml" <<'TOML'
name = "ArenaCore"
version = "0.1.0"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[lean_lib]]
name = "ArenaCore"
TOML
cp "$repo/source/lean-vendor/formal-core/lean-toolchain" "$pkg/source/lean-vendor/formal-core/lean-toolchain" 2>/dev/null \
  || printf 'leanprover/lean4:v4.34.1\n' > "$pkg/source/lean-vendor/formal-core/lean-toolchain"
cat > "$pkg/source/lean-vendor/spec/lean/lakefile.toml" <<'TOML'
name = "NearSpec"
version = "0.1.0"

[[lean_lib]]
name = "NearSpec"
globs = ["NearSpec.+"]

[[require]]
name = "ArenaCore"
path = "../../formal-core"
TOML
printf 'leanprover/lean4:v4.34.1\n' > "$pkg/source/lean-vendor/spec/lean/lean-toolchain"
cat > "$pkg/source/lean-vendor/spec/lean/v3/lakefile.toml" <<'TOML'
name = "NearSpecV3"
version = "0.1.0"

[[lean_lib]]
name = "NearSpecV3"
globs = ["NearSpecV3.+"]

[[require]]
name = "NearSpec"
path = ".."

[[require]]
name = "ArenaCore"
path = "../../../formal-core"
TOML
printf 'leanprover/lean4:v4.34.1\n' > "$pkg/source/lean-vendor/spec/lean/v3/lean-toolchain"

( cd "$pkg/source/lean-vendor" && find . -type f ! -path './*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) \
  > "$pkg/dependency-locks/lean-vendor.sha256"
( cd "$pkg/formal" && find ZkFormal ReexecV3D0 -type f -name '*.lean' 2>/dev/null | LC_ALL=C sort | xargs sha256sum ) \
  > "$pkg/dependency-locks/zk-formal.sha256"
echo "lean-vendor: $(wc -l < "$pkg/dependency-locks/lean-vendor.sha256") files; candidate: $(wc -l < "$pkg/dependency-locks/zk-formal.sha256") files (PIN ${PIN:0:7})"
