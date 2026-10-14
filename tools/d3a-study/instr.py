"""Instrumented run of the independent Python D3 checker (read-only use of repo code).
Counts executed flat-IR instructions per original WASM opcode, gas charge points, host calls,
memory sizes, bulk-memory bytes and host memory traffic, per case."""
import sys, os, json, types, collections, time
REPO = os.environ.get("REPO", "/data/illia/nearproof-wt/v3-d3a-study")
CR = os.path.join(REPO, "oracle/wasm-d3/cleanroom")
TOOLS = os.path.join(REPO, "oracle/tools")
sys.path.insert(0, TOOLS); sys.path.insert(0, CR)
src = open(os.path.join(CR, "nearwasm.py")).read()
a = "            op = ins[0]\n"
assert src.count(a) == 1
src = src.replace(a, a + "            _CNT[id(code)][pc - 1] += 1\n")
b = "    f.code = code\n"
assert src.count(b) == 1
src = src.replace(b, b + """    _orig = [None] * len(code)
    _orig[0] = 'charge'
    for _pc in range(n):
        for _ci in range(idx_of[_pc], idx_of[_pc + 1]):
            _orig[_ci] = 'charge' if code[_ci][0] in (O_CHARGE, O_CHARGEL) else ops[_pc][0]
    _REG[id(code)] = (code, _orig)
    _CNT[id(code)] = [0] * len(code)
""")
W = types.ModuleType("nearwasm"); W.__file__ = os.path.join(CR, "nearwasm.py")
W._CNT = {}; W._REG = {}
sys.modules["nearwasm"] = W
exec(compile(src, W.__file__, "exec"), W.__dict__)
import spec_check_v3_d3 as S
HOST = collections.Counter(); HOSTGAS = collections.Counter()
_hd = W.host_dispatch
def host_dispatch(inst, name, a):
    HOST[name] += 1
    b0 = inst.gc.burnt
    try:
        return _hd(inst, name, a)
    finally:
        HOSTGAS[name] += inst.gc.burnt - b0
W.host_dispatch = host_dispatch
MEMIO = collections.Counter()
for fn in ("mem_read", "mem_write"):
    orig = getattr(W, fn)
    def wrap(inst, ptr, x, _o=orig, _fn=fn):
        MEMIO[_fn + "_calls"] += 1
        MEMIO[_fn + "_bytes"] += (x if isinstance(x, int) else len(x))
        return _o(inst, ptr, x)
    setattr(W, fn, wrap)
CALLS = []
_rv = S.run_vm
def run_vm(prep, code, method, prepaid, cap, ctx, ext, store, storage_usage):
    before = sum(sum(v) for v in W._CNT.values())
    hb = sum(HOST.values())
    _se = W.sync_exit; mem = [0]
    def se(inst):
        mem[0] = max(mem[0], getattr(inst, "memlen", 0)); return _se(inst)
    W.sync_exit = se
    try:
        r = _rv(prep, code, method, prepaid, cap, ctx, ext, store, storage_usage)
    finally:
        W.sync_exit = _se
    CALLS.append(dict(code_len=len(code), instrs=sum(sum(v) for v in W._CNT.values()) - before,
                      host=sum(HOST.values()) - hb, pages=mem[0] // 65536, burnt=r.get("burnt", 0),
                      aborted=r.get("aborted")))
    return r
S.run_vm = run_vm

def snapshot():
    op = collections.Counter(); charge_gas = 0
    for k, cnt in W._CNT.items():
        code, orig = W._REG[k]
        for ci, c in enumerate(cnt):
            if c:
                op[orig[ci]] += c
                if code[ci][0] == W.O_CHARGE: charge_gas += c * code[ci][1]
    return op, charge_gas

out = open(sys.argv[1], "w")
for d in sys.argv[2:]:
    for k in W._CNT: W._CNT[k] = [0] * len(W._CNT[k])
    HOST.clear(); HOSTGAS.clear(); MEMIO.clear(); CALLS.clear()
    t = time.time()
    v = S.check_case(d)
    op, cg = snapshot()
    out.write(json.dumps(dict(case=d, verdict=v, secs=time.time() - t, ops={str(k): c for k, c in op.items()},
        charge_gas=cg, host=dict(HOST), hostgas=dict(HOSTGAS), memio=dict(MEMIO), calls=CALLS)) + "\n")
    out.flush()
