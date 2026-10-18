"""Tiny Wasm assembler for the family-F1 test programs (one exported function, no imports).

A program is a dict {name, result: None|'i32'|'i64', locals: [types], body: [instr...]}; an
instruction is a tuple ('i32.const', v), ('br', l), ('block', None|'i32'|'i64'), ('loop',),
('end',), ('local.get', i), or a bare mnemonic string ('i64.add').  The implicit final `end` of the
body is appended.  Optional `memory`: emit a 1-page memory (nearcore requires none here).
"""

VT = {'i32': 0x7F, 'i64': 0x7E}
NUM = {
    'i32.eqz': 0x45, 'i32.eq': 0x46, 'i32.ne': 0x47, 'i32.lt_s': 0x48, 'i32.lt_u': 0x49,
    'i32.gt_s': 0x4A, 'i32.gt_u': 0x4B, 'i32.le_s': 0x4C, 'i32.le_u': 0x4D, 'i32.ge_s': 0x4E,
    'i32.ge_u': 0x4F,
    'i64.eqz': 0x50, 'i64.eq': 0x51, 'i64.ne': 0x52, 'i64.lt_s': 0x53, 'i64.lt_u': 0x54,
    'i64.gt_s': 0x55, 'i64.gt_u': 0x56, 'i64.le_s': 0x57, 'i64.le_u': 0x58, 'i64.ge_s': 0x59,
    'i64.ge_u': 0x5A,
    'i32.add': 0x6A, 'i32.sub': 0x6B, 'i32.mul': 0x6C, 'i32.and': 0x71, 'i32.or': 0x72,
    'i32.xor': 0x73, 'i32.shl': 0x74, 'i32.shr_s': 0x75, 'i32.shr_u': 0x76, 'i32.rotl': 0x77,
    'i32.rotr': 0x78,
    'i64.add': 0x7C, 'i64.sub': 0x7D, 'i64.mul': 0x7E, 'i64.and': 0x83, 'i64.or': 0x84,
    'i64.xor': 0x85, 'i64.shl': 0x86, 'i64.shr_s': 0x87, 'i64.shr_u': 0x88, 'i64.rotl': 0x89,
    'i64.rotr': 0x8A,
    'drop': 0x1A, 'select': 0x1B, 'return': 0x0F, 'end': 0x0B, 'nop': 0x01,
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
    if op in ('local.get', 'local.set', 'local.tee'):
        return bytes([{'local.get': 0x20, 'local.set': 0x21, 'local.tee': 0x22}[op]]) + uleb(i[1])
    raise ValueError(op)


def section(sid, payload):
    return bytes([sid]) + uleb(len(payload)) + payload


def vec(items):
    return uleb(len(items)) + b''.join(items)


def assemble(prog):
    res = [] if prog.get('result') is None else [VT[prog['result']]]
    ftype = b'\x60' + vec([]) + vec([bytes([r]) for r in res])
    locs = prog.get('locals', [])
    groups = []
    for t in locs:
        if groups and groups[-1][1] == t:
            groups[-1][0] += 1
        else:
            groups.append([1, t])
    body = vec([uleb(n) + bytes([VT[t]]) for n, t in groups])
    body += b''.join(instr(i) for i in prog['body']) + b'\x0B'
    name = prog.get('export', 'main').encode()
    return (b'\x00asm\x01\x00\x00\x00' + section(1, vec([ftype])) + section(3, vec([uleb(0)])) +
            section(7, vec([uleb(len(name)) + name + b'\x00' + uleb(0)])) +
            section(10, vec([uleb(len(body)) + body])))
