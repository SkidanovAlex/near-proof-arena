"""Experimental fixed SHA-384 compression graph using nibble lookup relations.
Executable relation only: no AIR/PCS, lookup argument or Lean certificate yet.
Inputs: 128 little-endian state nibbles, 256 little-endian message-word nibbles.
"""
import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
SPEC = REPO/'spec/lean/v3/NearSpecV3/SHA512.lean'


def constants():
    text = SPEC.read_text().split('def K : List Nat :=', 1)[1].split(']', 1)[0]
    result = [int(x, 16) for x in re.findall(r'0x[0-9a-fA-F]+', text)]
    assert len(result) == 80
    return result


def relation(op, args):
    assert all(type(x) is int and 0 <= x < 16 for x in args)
    if op == 'xor3': return args[0] ^ args[1] ^ args[2]
    if op == 'choose': return (args[0] & args[1]) ^ ((15 ^ args[0]) & args[2])
    if op == 'majority': return (args[0] & args[1]) ^ (args[0] & args[2]) ^ (args[1] & args[2])
    if op.startswith('splice'):
        shift = int(op[-1]); assert shift in (1, 2, 3)
        return (args[0] >> shift) | ((args[1] & ((1 << shift)-1)) << (4-shift))
    raise ValueError('unknown lookup')


class Graph:
    def __init__(self):
        self.size = 384
        self.gates = []
        self.constants = {}
        self.phase = ('input', 0)
        self.gate_phases = []
        self.words = []
    def emit(self, gate):
        self.gates.append(gate)
        self.gate_phases.append(self.phase)
    def const(self, value):
        assert 0 <= value < 16
        if value not in self.constants:
            self.constants[value] = self.size
            self.emit(('const', (), (self.size,), value)); self.size += 1
        return self.constants[value]
    def lookup(self, op, inputs):
        output = self.size; self.size += 1
        self.emit((op, tuple(inputs), (output,), 0))
        return output
    def rotate(self, word, bits, shift=False):
        q, r = divmod(bits, 4)
        def at(i): return self.const(0) if shift and i >= 16 else word[i % 16]
        return [self.lookup('splice'+str(r), [at(i+q), at(i+q+1)]) if r else at(i+q) for i in range(16)]
    def boolean(self, op, *words):
        return [self.lookup(op, inputs) for inputs in zip(*words)]
    def add(self, *words):
        assert 2 <= len(words) <= 5
        carry = self.const(0); result = []
        for inputs in zip(*words):
            out, nxt = self.size, self.size+1; self.size += 2
            self.emit(('add', tuple(inputs)+(carry,), (out, nxt), len(words)))
            result.append(out); carry = nxt
        self.words.append(tuple(result))
        return result
    def sigma(self, word, rotations, last_shift=False):
        return self.boolean('xor3', *(self.rotate(word, r, last_shift and i == 2) for i, r in enumerate(rotations)))


def compile_graph():
    g = Graph()
    initial = [list(range(16*i, 16*(i+1))) for i in range(8)]
    words = [list(range(128+16*i, 128+16*(i+1))) for i in range(16)]
    g.words.extend(tuple(w) for w in initial+words)
    for i in range(16, 80):
        g.phase = ('schedule', i)
        s0 = g.sigma(words[i-15], (1, 8, 7), True)
        s1 = g.sigma(words[i-2], (19, 61, 6), True)
        words.append(g.add(words[i-16], s0, words[i-7], s1))
    a, b, c, d, e, f, h0, h1 = initial
    for round_index, (k, word) in enumerate(zip(constants(), words)):
        g.phase = ('round', round_index)
        kw = [g.const((k >> (4*i)) & 15) for i in range(16)]
        t1 = g.add(h1, g.sigma(e, (14, 18, 41)), g.boolean('choose', e, f, h0), kw, word)
        t2 = g.add(g.sigma(a, (28, 34, 39)), g.boolean('majority', a, b, c))
        a, b, c, d, e, f, h0, h1 = g.add(t1, t2), a, b, c, g.add(d, t1), e, f, h0
    g.phase = ('endpoint', 0)
    g.outputs = [g.add(x, y) for x, y in zip(initial, (a, b, c, d, e, f, h0, h1))]
    return g


def inputs(state, block):
    assert len(state) == 8 and len(block) == 128
    words = list(state)+[int.from_bytes(block[i:i+8], 'big') for i in range(0, 128, 8)]
    assert all(type(w) is int and 0 <= w < 1 << 64 for w in words)
    return [(w >> (4*i)) & 15 for w in words for i in range(16)]


def witness(g, source):
    values = list(source)
    assert len(values) == 384
    for op, ins, outs, bound in g.gates:
        assert outs[0] == len(values) and all(i < outs[0] for i in ins)
        args = [values[i] for i in ins]
        if op == 'const': values.append(bound)
        elif op == 'add':
            total = sum(args); values.extend([total % 16, total // 16])
        else: values.append(relation(op, args))
    assert len(values) == g.size
    return values


def check(g, source, values, expected):
    assert len(values) == g.size and values[:384] == source
    assert all(type(v) is int and 0 <= v < 16 for v in values)
    for op, ins, outs, bound in g.gates:
        args = [values[i] for i in ins]
        if op == 'const': assert values[outs[0]] == bound
        elif op == 'add':
            # Exact integer equation; magnitudes below 80, hence no Fp wrap.
            assert args[-1] < bound and values[outs[1]] < bound
            assert sum(args) == values[outs[0]] + 16*values[outs[1]]
        else: assert values[outs[0]] == relation(op, args)
    result = [sum(values[j] << (4*i) for i, j in enumerate(word)) for word in g.outputs]
    assert result == list(expected)
    return True
