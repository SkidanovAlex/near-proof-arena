"""Tiny Wasm assembler for the family-F1 test programs (one exported function, no imports).

A program is a dict {name, result: None|'i32'|'i64', locals: [types], body: [instr...]}; an
instruction is a tuple ('i32.const', v), ('br', l), ('block', None|'i32'|'i64'), ('loop',),
('end',), ('local.get', i), or a bare mnemonic string ('i64.add').  The implicit final `end` of the
body is appended.  Optional `data`: a list of `(offset, bytes)` active data segments (a memory
section with one page is emitted when `memory` or `data` is present).  Memory instructions are
`('i32.load', offset)` etc. (natural alignment).  Optional `globals`: a list of `(type, mutable, init)`
module globals with constant initialisers, accessed by `('global.get', g)` / `('global.set', g)`.
"""

VT = {'i32': 0x7F, 'i64': 0x7E}
NUM = {
    'i32.eqz': 0x45, 'i32.eq': 0x46, 'i32.ne': 0x47, 'i32.lt_s': 0x48, 'i32.lt_u': 0x49,
    'i32.gt_s': 0x4A, 'i32.gt_u': 0x4B, 'i32.le_s': 0x4C, 'i32.le_u': 0x4D, 'i32.ge_s': 0x4E,
    'i32.ge_u': 0x4F,
    'i64.eqz': 0x50, 'i64.eq': 0x51, 'i64.ne': 0x52, 'i64.lt_s': 0x53, 'i64.lt_u': 0x54,
    'i64.gt_s': 0x55, 'i64.gt_u': 0x56, 'i64.le_s': 0x57, 'i64.le_u': 0x58, 'i64.ge_s': 0x59,
    'i64.ge_u': 0x5A,
    'i32.add': 0x6A, 'i32.sub': 0x6B, 'i32.mul': 0x6C, 'i32.div_s': 0x6D, 'i32.div_u': 0x6E,
    'i32.rem_s': 0x6F, 'i32.rem_u': 0x70, 'i32.and': 0x71, 'i32.or': 0x72,
    'i32.xor': 0x73, 'i32.shl': 0x74, 'i32.shr_s': 0x75, 'i32.shr_u': 0x76, 'i32.rotl': 0x77,
    'i32.rotr': 0x78,
    'i64.add': 0x7C, 'i64.sub': 0x7D, 'i64.mul': 0x7E, 'i64.div_s': 0x7F, 'i64.div_u': 0x80,
    'i64.rem_s': 0x81, 'i64.rem_u': 0x82, 'i64.and': 0x83, 'i64.or': 0x84,
    'i64.xor': 0x85, 'i64.shl': 0x86, 'i64.shr_s': 0x87, 'i64.shr_u': 0x88, 'i64.rotl': 0x89,
    'i64.rotr': 0x8A,
    'drop': 0x1A, 'select': 0x1B, 'return': 0x0F, 'end': 0x0B, 'nop': 0x01,
}


MEM = {
    'i32.load': (0x28, 2), 'i64.load': (0x29, 3), 'i32.load8_s': (0x2C, 0), 'i32.load8_u': (0x2D, 0),
    'i32.load16_s': (0x2E, 1), 'i32.load16_u': (0x2F, 1), 'i64.load8_s': (0x30, 0), 'i64.load8_u': (0x31, 0),
    'i64.load16_s': (0x32, 1), 'i64.load16_u': (0x33, 1), 'i64.load32_s': (0x34, 2), 'i64.load32_u': (0x35, 2),
    'i32.store': (0x36, 2), 'i64.store': (0x37, 3), 'i32.store8': (0x3A, 0), 'i32.store16': (0x3B, 1),
    'i64.store8': (0x3C, 0), 'i64.store16': (0x3D, 1), 'i64.store32': (0x3E, 2),
}


def uleb(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def sleb(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if (n == 0 and not b & 0x40) or (n == -1 and b & 0x40):
            out.append(b)
            return bytes(out)
        out.append(b | 0x80)


def signed(v, w):
    v &= (1 << w) - 1
    return v - (1 << w) if v >> (w - 1) else v


def instr(i):
    if isinstance(i, str):
        i = (i,)
    op = i[0]
    if op in NUM:
        return bytes([NUM[op]])
    if op == 'i32.const':
        return b'\x41' + sleb(signed(i[1], 32))
    if op == 'i64.const':
        return b'\x42' + sleb(signed(i[1], 64))
    if op in ('block', 'loop'):
        bt = i[1] if len(i) > 1 else None
        return bytes([0x02 if op == 'block' else 0x03, 0x40 if bt is None else VT[bt]])
    if op in ('br', 'br_if'):
        return bytes([0x0C if op == 'br' else 0x0D]) + uleb(i[1])
    if op in MEM:
        code, align = MEM[op]
        return bytes([code]) + uleb(align) + uleb(i[1] if len(i) > 1 else 0)
    if op in ('local.get', 'local.set', 'local.tee'):
        return bytes([{'local.get': 0x20, 'local.set': 0x21, 'local.tee': 0x22}[op]]) + uleb(i[1])
    if op in ('global.get', 'global.set'):
        return bytes([0x23 if op == 'global.get' else 0x24]) + uleb(i[1])
    if op == 'call':
        return b'\x10' + uleb(i[1])
    raise ValueError(op)


def section(sid, payload):
    return bytes([sid]) + uleb(len(payload)) + payload


def vec(items):
    return uleb(len(items)) + b''.join(items)


def func_body(f):
    locs = f.get('locals', [])
    groups = []
    for t in locs:
        if groups and groups[-1][1] == t:
            groups[-1][0] += 1
        else:
            groups.append([1, t])
    body = vec([uleb(n) + bytes([VT[t]]) for n, t in groups])
    body += b''.join(instr(i) for i in f['body']) + b'\x0B'
    return uleb(len(body)) + body


def assemble(prog):
    """Function 0 (`imports` count aside) is `prog` (exported); `prog['funcs']` are the following
    functions.  `prog['imports']` is a list of `(module, name, params, result)`, in import order;
    they occupy function indices `0 .. nimp-1`, so `prog` is function `nimp`."""
    imports = prog.get('imports', [])
    funcs = [prog] + prog.get('funcs', [])
    types = []
    for _, _, params, result in imports:
        res = [] if result is None else [VT[result]]
        types.append(b'\x60' + vec([bytes([VT[t]]) for t in params]) + vec([bytes([r]) for r in res]))
    for f in funcs:
        res = [] if f.get('result') is None else [VT[f['result']]]
        types.append(b'\x60' + vec([bytes([VT[t]]) for t in f.get('params', [])]) + vec([bytes([r]) for r in res]))
    name = prog.get('export', 'main').encode()
    isec = b''
    if imports:
        isec = section(2, vec([uleb(len(m)) + m.encode() + uleb(len(n)) + n.encode() + b'\x00' + uleb(k)
                               for k, (m, n, _, _) in enumerate(imports)]))
    data = prog.get('data', [])
    mem = b''
    if prog.get('memory') or data:
        mem = section(5, vec([b'\x00' + uleb(1)]))
    gsec = b''
    if prog.get('globals'):
        gsec = section(6, vec([bytes([VT[t], 1 if m else 0]) + instr((f'{t}.const', v)) + b'\x0B'
                                for t, m, v in prog['globals']]))
    dsec = b''
    if data:
        dsec = section(11, vec([b'\x00\x41' + sleb(off) + b'\x0B' + uleb(len(bs)) + bytes(bs) for off, bs in data]))
    return (b'\x00asm\x01\x00\x00\x00' + section(1, vec(types)) + isec +
            section(3, vec([uleb(len(imports) + k) for k in range(len(funcs))])) +
            mem + gsec + section(7, vec([uleb(len(name)) + name + b'\x00' + uleb(len(imports))])) +
            section(10, vec([func_body(f) for f in funcs])) + dsec)
