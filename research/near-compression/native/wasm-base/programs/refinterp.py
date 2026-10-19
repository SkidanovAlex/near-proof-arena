"""Independent reference interpreter for family F1 (written from the WebAssembly 2.0 spec, §4.3.2 and
§4.4.8; it shares no code with the Lean spec or the Rust trace generator).  Returns the result
value and the number of executed instructions (excluding the implicit function prologue)."""

M32, M64 = (1 << 32) - 1, (1 << 64) - 1


def sg(v, w):
    return v - (1 << w) if v >> (w - 1) else v


class Trap(Exception):
    pass


def tdiv(x, y):
    q = abs(x) // abs(y)
    return q if (x >= 0) == (y >= 0) else -q


def binop(name, a, b):
    w = 64 if name.startswith('i64') else 32
    m = (1 << w) - 1
    op = name[4:]
    k = b % w
    if op == 'add': return (a + b) & m
    if op == 'sub': return (a - b) & m
    if op == 'mul': return (a * b) & m
    if op in ('div_s', 'div_u', 'rem_s', 'rem_u'):
        if b == 0: raise Trap('div by zero')
        if op == 'div_u': return a // b
        if op == 'rem_u': return a % b
        x, y = sg(a, w), sg(b, w)
        q = tdiv(x, y)
        if op == 'div_s':
            if q == 1 << (w - 1): raise Trap('overflow')
            return q & m
        return (x - q * y) & m
    if op == 'and': return a & b
    if op == 'or': return a | b
    if op == 'xor': return a ^ b
    if op == 'shl': return (a << k) & m
    if op == 'shr_u': return a >> k
    if op == 'shr_s': return (sg(a, w) >> k) & m
    if op == 'rotl': return ((a << k) | (a >> ((w - k) % w))) & m if k else a
    if op == 'rotr': return ((a >> k) | (a << ((w - k) % w))) & m if k else a
    if op == 'eq': return int(a == b)
    if op == 'ne': return int(a != b)
    if op == 'lt_s': return int(sg(a, w) < sg(b, w))
    if op == 'lt_u': return int(a < b)
    if op == 'gt_s': return int(sg(a, w) > sg(b, w))
    if op == 'gt_u': return int(a > b)
    if op == 'le_s': return int(sg(a, w) <= sg(b, w))
    if op == 'le_u': return int(a <= b)
    if op == 'ge_s': return int(sg(a, w) >= sg(b, w))
    if op == 'ge_u': return int(a >= b)
    raise ValueError(name)


def run(prog, fuel=10 ** 8):
    body = [i if isinstance(i, tuple) else (i,) for i in prog['body']] + [('end',)]
    # matching ends
    end_of, stack = {}, []
    for pc, i in enumerate(body):
        if i[0] in ('block', 'loop'):
            stack.append(pc)
        elif i[0] == 'end':
            if stack:
                end_of[stack.pop()] = pc
    loc = [0] * len(prog.get('locals', []))
    mem = {}
    for off, bs in prog.get('data', []):
        for k, x in enumerate(bs):
            mem[off + k] = x

    LOADS = {'i32.load': (4, False, 32), 'i64.load': (8, False, 64), 'i32.load8_s': (1, True, 32),
             'i32.load8_u': (1, False, 32), 'i32.load16_s': (2, True, 32), 'i32.load16_u': (2, False, 32),
             'i64.load8_s': (1, True, 64), 'i64.load8_u': (1, False, 64), 'i64.load16_s': (2, True, 64),
             'i64.load16_u': (2, False, 64), 'i64.load32_s': (4, True, 64), 'i64.load32_u': (4, False, 64)}
    STORES = {'i32.store': 4, 'i64.store': 8, 'i32.store8': 1, 'i32.store16': 2, 'i64.store8': 1,
              'i64.store16': 2, 'i64.store32': 4}
    st = []
    labels = [('func', len(body), 1 if prog.get('result') else 0, 0)]  # kind, target, arity, height
    pc, n = 0, 0

    def branch(l):
        nonlocal pc
        kind, tgt, ar, h = labels[-1 - l]
        vals = st[len(st) - ar:] if ar else []
        del st[h:]
        st.extend(vals)
        if kind == 'func':
            return True
        del labels[len(labels) - (l if kind == 'loop' else l + 1):]
        pc = tgt
        return False

    while True:
        n += 1
        if n > fuel:
            raise RuntimeError('fuel')
        i = body[pc]
        op = i[0]
        if op in ('i32.const', 'i64.const'):
            st.append(i[1] & (M32 if op[1] == '3' else M64)); pc += 1
        elif op == 'drop':
            st.pop(); pc += 1
        elif op == 'select':
            c = st.pop(); v2 = st.pop(); v1 = st.pop(); st.append(v1 if c else v2); pc += 1
        elif op == 'local.get':
            st.append(loc[i[1]]); pc += 1
        elif op == 'local.set':
            loc[i[1]] = st.pop(); pc += 1
        elif op == 'local.tee':
            loc[i[1]] = st[-1]; pc += 1
        elif op in LOADS:
            w, sgn, rw = LOADS[op]
            ea = st.pop() + (i[1] if len(i) > 1 else 0)
            v = sum(mem.get(ea + k, 0) << (8 * k) for k in range(w))
            if sgn and v >> (8 * w - 1):
                v = (v - (1 << (8 * w))) & ((1 << rw) - 1)
            st.append(v); pc += 1
        elif op in STORES:
            w = STORES[op]
            v = st.pop()
            ea = st.pop() + (i[1] if len(i) > 1 else 0)
            for k in range(w):
                mem[ea + k] = (v >> (8 * k)) & 0xFF
            pc += 1
        elif op in ('i32.eqz', 'i64.eqz'):
            st.append(int(st.pop() == 0)); pc += 1
        elif op == 'block':
            ar = 0 if len(i) < 2 or i[1] is None else 1
            labels.append(('block', end_of[pc] + 1, ar, len(st))); pc += 1
        elif op == 'loop':
            labels.append(('loop', pc + 1, 0, len(st))); pc += 1
        elif op == 'end':
            if len(labels) == 1:
                return (st[-1] if st else None), n
            labels.pop(); pc += 1
        elif op == 'br':
            if branch(i[1]): return (st[-1] if st else None), n
        elif op == 'br_if':
            c = st.pop()
            if c:
                if branch(i[1]): return (st[-1] if st else None), n
            else:
                pc += 1
        elif op == 'return':
            return (st[-1] if st else None), n
        else:
            b = st.pop(); a = st.pop()
            try:
                st.append(binop(op, a, b))
            except Trap:
                return 'trap', n
            pc += 1
