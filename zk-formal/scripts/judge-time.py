#!/usr/bin/env python3
"""Judge-style elaboration timing of a certificate's candidate import closure.

Mirrors runners/formal-checker/src/pipeline.rs `compile()` for the candidate stage: every
candidate module of the import closure is elaborated serially, in dependency order, by a
plain `lean -R <root> -o X.olean -i X.ilean X.lean` (no lake, no -D options, no C), against
warm trusted `.olean`s (ArenaCore / NearSpec / NearSpecV3 lake builds) and a fresh output
directory for the candidate modules.  Run it single-core (taskset) for comparable numbers.

usage: judge-time.py OUTDIR ROOT_MODULE... [--limit N] [--dry]
  OUTDIR/times.tsv   module  seconds  (appended as it goes; a rerun resumes)
  OUTDIR/order.txt   the topological order
  OUTDIR/out/        candidate .olean/.ilean
"""
import os, re, subprocess, sys, time

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.abspath(os.path.join(here, "..", ".."))
# JT_SRC: read candidate sources from a snapshot with the same layout (so the tree can be edited
# while a long measurement runs); trusted .oleans always come from this checkout.
src_repo = os.environ.get("JT_SRC", repo)
CAND = [("NpUdrStarkV2", "examples/np-udr-stark-v2/formal"),
        ("ZkFormal", "zk-formal"),
        ("ReexecV3D0", "examples/reexec-v3-d0/formal")]
TRUSTED = [("ArenaCore", "formal-core"), ("NearSpecV3", "spec/lean/v3"), ("NearSpec", "spec/lean")]
TRUSTED_OLEANS = [os.path.join(repo, d, ".lake/build/lib/lean") for _, d in TRUSTED]
TOOLCHAIN = ("Init", "Std", "Lean", "Lake")
# the pinned toolchain's `lean` (no elan proxy: the judge runs its toolchain binary directly)
_tc = open(os.path.join(repo, "zk-formal", "lean-toolchain")).read().strip()
LEAN = os.environ.get("LEAN") or os.path.expanduser(
    "~/.elan/toolchains/" + _tc.replace("/", "--").replace(":", "---") + "/bin/lean")


def source_of(mod):
    for root, d in CAND:
        if mod == root or mod.startswith(root + "."):
            p = os.path.join(src_repo, d, *mod.split(".")) + ".lean"
            if os.path.isfile(p):
                return os.path.join(src_repo, d), p
    return None, None


def imports(path):
    txt = open(path, encoding="utf-8").read()
    txt = re.sub(r"/-.*?-/", "", txt, flags=re.S)
    txt = re.sub(r"--[^\n]*", "", txt)
    return re.findall(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.']+)", txt, flags=re.M)


def closure(roots):
    deps, todo = {}, list(roots)
    while todo:
        m = todo.pop()
        if m in deps:
            continue
        _, p = source_of(m)
        if p is None:
            r = m.split(".")[0]
            if r in TOOLCHAIN or any(r == t for t, _ in TRUSTED) or m == "ArenaExpectedInst":
                continue
            sys.exit(f"judge-time: cannot resolve {m}")
        deps[m] = [i for i in imports(p) if source_of(i)[1] is not None]
        todo += deps[m]
    order, state = [], {}
    def visit(m):  # iterative DFS
        stack = [(m, iter(deps[m]))]
        state[m] = 1
        while stack:
            n, it = stack[-1]
            for c in it:
                if state.get(c) is None:
                    state[c] = 1
                    stack.append((c, iter(deps[c])))
                    break
            else:
                stack.pop(); state[n] = 2; order.append(n)
    for m in sorted(deps):
        if state.get(m) is None:
            visit(m)
    return order, deps


def main():
    args = sys.argv[1:]
    limit, dry = None, False
    if "--limit" in args:
        i = args.index("--limit"); limit = int(args[i + 1]); del args[i:i + 2]
    if "--dry" in args:
        args.remove("--dry"); dry = True
    out, roots = os.path.abspath(args[0]), args[1:]
    order, _ = closure(roots)
    os.makedirs(os.path.join(out, "out"), exist_ok=True)
    open(os.path.join(out, "order.txt"), "w").write("\n".join(order) + "\n")
    print(f"judge-time: {len(order)} candidate modules", flush=True)
    if dry:
        return
    tsv = os.path.join(out, "times.tsv")
    done = {}
    if os.path.exists(tsv):
        for ln in open(tsv):
            m, s = ln.split("\t")[:2]
            done[m] = float(s)
    env = dict(os.environ)
    env["LEAN_PATH"] = ":".join(TRUSTED_OLEANS + [os.path.join(out, "out")])
    total = sum(done.values())
    with open(tsv, "a") as f:
        for n, m in enumerate(order):
            if limit is not None and n >= limit:
                break
            stem = os.path.join(out, "out", *m.split("."))
            if m in done and os.path.exists(stem + ".olean"):
                continue
            root, src = source_of(m)
            os.makedirs(os.path.dirname(stem), exist_ok=True)
            t0 = time.monotonic()
            r = subprocess.run([LEAN, "-R", root, "-o", stem + ".olean", "-i", stem + ".ilean", src],
                               env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            dt = time.monotonic() - t0
            if r.returncode != 0:
                sys.stdout.write(r.stdout.decode(errors="replace")[-3000:])
                sys.exit(f"judge-time: {m} failed ({r.returncode})")
            total += dt
            f.write(f"{m}\t{dt:.2f}\n"); f.flush()
            if dt >= 10:
                print(f"[{n + 1}/{len(order)}] {m} {dt:.1f}s (total {total:.0f}s)", flush=True)
    print(f"judge-time: total {total:.1f}s over {len(order)} modules", flush=True)


main()
