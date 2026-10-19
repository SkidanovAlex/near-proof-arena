#!/usr/bin/env python3
"""Generate the family-F1 test programs (`<out>/<name>.wasm` + `<out>/<name>.json` with the
independent reference result from refinterp.py).  Usage: gen.py <out_dir> [hash_iters...]"""
import json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wasmasm import assemble, NUM
from refinterp import run

BIN = ['add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'shr_s', 'shr_u', 'rotl', 'rotr']
REL = ['eq', 'ne', 'lt_s', 'lt_u', 'gt_s', 'gt_u', 'le_s', 'le_u', 'ge_s', 'ge_u']


def edge(w, rng):
    m = (1 << w) - 1
    vals = [0, 1, 2, 3, 7, 8, (1 << (w - 1)) - 1, 1 << (w - 1), (1 << (w - 1)) + 1, m, m - 1,
            0x8000, 0xFFFF, 0x10000, 0x7FFFFFFF, 0x80000000, w - 1, w, w + 1, 2 * w + 3]
    vals += [rng.getrandbits(w) for _ in range(6)] + [rng.getrandbits(8) for _ in range(3)]
    return [v & m for v in vals]


DIV = ['div_s', 'div_u', 'rem_s', 'rem_u']


def no_trap(op, a, b, w):
    if b == 0:
        return False
    return not (op == 'div_s' and a == 1 << (w - 1) and b == (1 << w) - 1)


def kat(t, op, rng, npairs=24):
    w = 64 if t == 'i64' else 32
    rel = op in REL or op == 'eqz'
    acc_t = 'i32' if rel else t
    body = []
    vals = edge(w, rng)
    pairs = [(rng.choice(vals), rng.choice(vals)) for _ in range(npairs)]
    if op in DIV:
        m = (1 << w) - 1
        pairs = [(1 << (w - 1), m), (m, 1), (1 << (w - 1), 1), (7, m), (m - 6, 3), (5, 7)] + pairs
        pairs = [(a, b) for a, b in pairs if no_trap(op, a, b, w)]
        if op == 'div_s':
            pairs = [p for p in pairs]
        if op == 'rem_s':
            pairs = [(1 << (w - 1), m)] + pairs   # MIN rem -1 = 0 (no trap)
    for a, b in pairs:
        body += [('local.get', 0), (f'{acc_t}.const', 31), f'{acc_t}.mul', (f'{t}.const', a)]
        if op != 'eqz':
            body.append((f'{t}.const', b))
        body += [f'{t}.{op}', f'{acc_t}.add', ('local.set', 0)]
    body.append(('local.get', 0))
    return {'name': f'kat_{t}_{op}', 'result': acc_t, 'locals': [acc_t], 'body': body}


def ctrl():
    """Nested blocks with results, br/br_if (taken and not), loop, select, drop, return."""
    b = [
        ('i32.const', 0), ('local.set', 0),
        ('block', 'i32'),                      # result-carrying block, exited by br 0
          ('i32.const', 5), ('i32.const', 6), 'i32.add',
          ('block',),
            ('local.get', 0), ('br_if', 0),    # not taken (0)
            ('i32.const', 1), ('local.set', 0),
          ('end',),
          ('block',),
            ('local.get', 0), ('br_if', 0),    # taken (1)
            ('i32.const', 99), ('local.set', 0),
          ('end',),
          ('br', 0),
        ('end',),
        ('local.set', 1),                      # 11
        ('loop',),                             # count local0 up to 20
          ('local.get', 0), ('i32.const', 1), 'i32.add', ('local.tee', 0),
          ('i32.const', 20), 'i32.lt_u', ('br_if', 0),
        ('end',),
        ('local.get', 1), ('i32.const', 1000), ('local.get', 0), ('i32.const', 20), 'i32.eq', 'select',
        ('i32.const', 77), 'drop',
        ('local.get', 1), 'i32.mul', ('local.set', 1),
        ('block',), ('local.get', 0), ('i32.const', 20), 'i32.ne', ('br_if', 0),
          ('local.get', 1), 'return', ('end',),
        ('i32.const', 0),
    ]
    return {'name': 'ctrl', 'result': 'i32', 'locals': ['i32', 'i32'], 'body': b}


def hashloop(n):
    """A mixed i32/i64 hash loop: FNV-1a-style i64 step, rotations, shifts, compares, select,
    a conditional block; n iterations (≈ 46 instructions each)."""
    i, h, x = 0, 1, 2
    b = [
        ('i64.const', 0xcbf29ce484222325), ('local.set', h),
        ('i32.const', 0x12345678), ('local.set', x),
        ('loop',),
          ('local.get', h), ('local.get', i), 'i64.xor', ('i64.const', 0x100000001b3), 'i64.mul',
          ('i64.const', 13), 'i64.rotl', ('local.tee', h),
          ('local.get', h), ('i64.const', 7), 'i64.shr_u', 'i64.xor', ('local.set', h),
          ('local.get', x), ('i32.const', 3), 'i32.shl', ('local.get', x), ('i32.const', 2), 'i32.shr_s',
          'i32.xor', ('i32.const', 0x9e3779b9), 'i32.add', ('local.set', x),
          ('block',),
            ('local.get', x), ('i32.const', 0), 'i32.ge_s', ('br_if', 0),
            ('local.get', h), ('i64.const', 0xff00ff00ff00ff00), 'i64.and', ('local.set', h),
          ('end',),
          ('local.get', i), ('i64.const', 1), 'i64.add', ('local.tee', i),
          ('i64.const', n), 'i64.lt_u', ('br_if', 0),
        ('end',),
        ('local.get', h), ('local.get', h), ('i64.const', 17), 'i64.rotr', ('local.get', x),
        'i32.eqz', 'select',
    ]
    return {'name': f'hashloop{n}', 'result': 'i64', 'locals': ['i64', 'i64', 'i32'], 'body': b}


def divloop(n):
    """A div/rem-heavy loop (i64 div_u/rem_u/div_s/rem_s, i32 div_s/rem_u), n iterations."""
    i, h, x = 0, 1, 2
    b = [
        ('i64.const', 0x123456789abcdef1), ('local.set', h), ('i32.const', 0x7654321), ('local.set', x),
        ('loop',),
          ('local.get', h), ('local.get', i), ('i64.const', 3), 'i64.add', 'i64.div_u',
          ('local.get', h), ('i64.const', 1000003), 'i64.rem_u', 'i64.add',
          ('i64.const', 0x9e3779b97f4a7c15), 'i64.mul', ('local.set', h),
          ('local.get', h), ('i64.const', -7), 'i64.div_s', ('local.get', h), ('i64.const', 13), 'i64.rem_s',
          'i64.xor', ('local.get', h), 'i64.add', ('local.set', h),
          ('local.get', x), ('i32.const', -3), 'i32.div_s', ('local.get', x), ('i32.const', 97), 'i32.rem_u',
          'i32.add', ('i32.const', 0x9e3779b9), 'i32.xor', ('local.set', x),
          ('local.get', i), ('i64.const', 1), 'i64.add', ('local.tee', i),
          ('i64.const', n), 'i64.lt_u', ('br_if', 0),
        ('end',),
        ('local.get', h), ('local.get', x), 'drop',
    ]
    return {'name': f'divloop{n}', 'result': 'i64', 'locals': ['i64', 'i64', 'i32'], 'body': b}


def trap(t, kind):
    """A trapping program: some values left on the stack, then a trapping div/rem."""
    w = 64 if t == 'i64' else 32
    m = (1 << w) - 1
    a, b, op = {'zero_u': (12345, 0, 'div_u'), 'zero_rem': (7, 0, 'rem_s'), 'ovf': (1 << (w - 1), m, 'div_s')}[kind]
    body = [('local.get', 0), (f'{t}.const', 3), f'{t}.add', ('local.set', 0),
            (f'{t}.const', 99), (f'{t}.const', a), (f'{t}.const', b), f'{t}.{op}', f'{t}.add']
    return {'name': f'trap_{t}_{kind}', 'result': t, 'locals': [t], 'body': body}


LOADS32 = ['i32.load', 'i32.load8_s', 'i32.load8_u', 'i32.load16_s', 'i32.load16_u']
LOADS64 = ['i64.load', 'i64.load8_s', 'i64.load8_u', 'i64.load16_s', 'i64.load16_u', 'i64.load32_s',
           'i64.load32_u']
DATA0 = [0x01, 0x80, 0xFF, 0x7F, 0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x00, 0x80, 0x00, 0x00,
         0xFE, 0xFF, 0xFF, 0xFF, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x55]


def memkat():
    """Every integer load at aligned / unaligned / word-crossing addresses of a data segment, every
    integer store (fresh, overlapping the data, near a page edge), loads after the stores."""
    a32, a64 = 0, 1
    body = []
    def acc32(load, addr, off=0):
        return [('local.get', a32), ('i32.const', 31), 'i32.mul', ('i32.const', addr), (load, off), 'i32.add',
                ('local.set', a32)]
    def acc64(load, addr, off=0):
        return [('local.get', a64), ('i64.const', 31), 'i64.mul', ('i32.const', addr), (load, off), 'i64.add',
                ('local.set', a64)]
    addrs = [100, 101, 103, 107, 112, 116, 120]
    for addr in addrs:
        for l in LOADS32:
            body += acc32(l, addr)
        for l in LOADS64:
            body += acc64(l, addr)
    body += acc32('i32.load', 96, 5) + acc64('i64.load', 0, 109)
    stores = [('i32.store', 2000, 0xDEADBEEF), ('i64.store', 2003, 0x0123456789ABCDEF), ('i32.store8', 102, 0x1FF),
              ('i32.store16', 105, 0x8001), ('i64.store8', 65535, 0xAB), ('i64.store16', 65534, 0xCDEF),
              ('i64.store32', 110, 0xFFFFFFFF80000000), ('i32.store', 99, 0x80000001), ('i64.store', 65528, -2)]
    for op, addr, val in stores:
        t = 'i64' if op.startswith('i64') else 'i32'
        body += [('i32.const', addr), (f'{t}.const', val), op]
    for addr in [2000, 2001, 2003, 2007, 100, 101, 102, 105, 106, 110, 113, 99, 65528, 65531, 65534, 65535]:
        for l in ['i32.load8_s', 'i32.load16_u', 'i32.load16_s'] + (['i32.load'] if addr <= 65532 else []):
            body += acc32(l, addr)
        for l in ['i64.load8_u', 'i64.load32_s'] + (['i64.load'] if addr <= 65528 else []):
            body += acc64(l, addr)
    body += [('local.get', a64), ('local.get', a32), 'i32.eqz', 'select'] if False else [('local.get', a64)]
    return {'name': 'memkat', 'result': 'i64', 'locals': ['i32', 'i64'], 'body': body, 'data': [(100, DATA0)]}


def memloop(n):
    """An array loop: writes `n` i64 words, then reads them back through narrower loads; n
    iterations per pass."""
    i, h, s_ = 0, 1, 2
    base = 4096
    b = [
        ('i64.const', 0x9e3779b97f4a7c15), ('local.set', h),
        ('loop',),
          ('local.get', i), ('i32.const', 8), 'i32.mul', ('local.get', h), ('i64.store', base),
          ('local.get', h), ('i64.const', 0x100000001b3), 'i64.mul', ('i64.const', 29), 'i64.rotl',
          ('local.get', i), ('i32.const', 4), 'i32.mul', ('i64.load32_u', base), 'i64.xor', ('local.set', h),
          ('local.get', i), ('i32.const', 1), 'i32.add', ('local.tee', i),
          ('i32.const', n), 'i32.lt_u', ('br_if', 0),
        ('end',),
        ('i32.const', 0), ('local.set', i),
        ('loop',),
          ('local.get', s_), ('local.get', i), ('i32.const', 8), 'i32.mul', ('i64.load', base), 'i64.add',
          ('local.get', i), ('i32.const', 8), 'i32.mul', ('i64.load8_s', base + 3), 'i64.add',
          ('local.get', i), ('i32.const', 8), 'i32.mul', ('i64.load16_s', base + 5), 'i64.sub', ('local.set', s_),
          ('local.get', i), ('i32.const', 1), 'i32.add', ('local.tee', i),
          ('i32.const', n), 'i32.lt_u', ('br_if', 0),
        ('end',),
        ('local.get', s_),
    ]
    return {'name': f'memloop{n}', 'result': 'i64', 'locals': ['i32', 'i64', 'i64'], 'body': b, 'memory': True}


def globkat(n):
    """Globals: i32 / i64 mutable globals updated in a loop (get, set, mixed with locals), an
    immutable i64 global read every iteration, and a global swap through the stack."""
    i, t = 0, 1
    b = [
        ('loop',),
          ('global.get', 0), ('i32.const', 0x9E3779B9), 'i32.mul', ('local.get', i), 'i32.xor', ('global.set', 0),
          ('global.get', 1), ('i64.const', 0x100000001B3), 'i64.mul', ('global.get', 2), 'i64.add', ('i64.const', 23),
          'i64.rotl', ('global.set', 1),
          ('global.get', 3), ('global.get', 1), 'i64.xor', ('local.tee', t), ('global.set', 3),
          ('local.get', i), ('i32.const', 1), 'i32.add', ('local.tee', i),
          ('i32.const', n), 'i32.lt_u', ('br_if', 0),
        ('end',),
        # swap globals 1 and 3 through the stack
        ('global.get', 1), ('global.get', 3), ('global.set', 1), ('global.set', 3),
        ('global.get', 1), ('global.get', 3), 'i64.sub', ('global.get', 0), 'drop',
        ('local.get', t), 'i64.add',
    ]
    return {'name': f'globkat{n}', 'result': 'i64', 'locals': ['i32', 'i64'], 'body': b,
            'globals': [('i32', True, 0x80000001), ('i64', True, -3), ('i64', False, 0x123456789), ('i64', True, 7)]}


def main():
    out = sys.argv[1]
    iters = [int(a) for a in sys.argv[2:]] or [8, 64]
    os.makedirs(out, exist_ok=True)
    rng = random.Random(20261018)
    progs = [kat(t, op, rng) for t in ('i32', 'i64') for op in BIN + DIV + REL + ['eqz']]
    progs += [trap(t, k) for t in ('i32', 'i64') for k in ('zero_u', 'zero_rem', 'ovf')]
    progs += [ctrl()] + [hashloop(n) for n in iters] + [divloop(n) for n in iters]
    progs += [memkat()] + [memloop(n) for n in iters]
    progs += [globkat(n) for n in iters]
    for p in progs:
        res, steps = run(p)
        with open(os.path.join(out, p['name'] + '.wasm'), 'wb') as f:
            f.write(assemble(p))
        with open(os.path.join(out, p['name'] + '.json'), 'w') as f:
            json.dump({'name': p['name'], 'result': res, 'type': p['result'], 'steps': steps}, f)
    print(len(progs), 'programs')


if __name__ == '__main__':
    main()
