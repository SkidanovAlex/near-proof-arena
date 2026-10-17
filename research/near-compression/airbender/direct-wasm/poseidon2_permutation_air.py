"""Width32 Poseidon2 single-row permutation AIR; no sponge/security certificate.

Inputs and outputs live in the same row. Every remaining column has one acyclic
assignment constraint. No message framing, call binding, or digest truncation
is claimed here. Upstream M128 parameters are experimental for our PQ target.
"""
import gzip
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
P = 2013265921
C = lambda x: ['c', x % P]
V = lambda x: ['v', x, 0]
A = lambda x,y: ['+', x, y]
M = lambda x,y: ['*', x, y]
S = lambda x,y: A(x, ['-', y])


def add(xs):
    values = list(xs)
    while len(values) > 1:
        values = [A(values[i], values[i+1]) if i+1 < len(values) else values[i]
                  for i in range(0, len(values), 2)]
    return values[0] if values else C(0)


def constants():
    manifest = json.loads((ROOT/'results/hash-architecture-review/sources.json').read_bytes())
    item = next(x for x in manifest['code'] if x['path']=='baby-bear/src/poseidon2.rs')
    raw = gzip.decompress((ROOT/item['snapshot']).read_bytes())
    assert hashlib.sha256(raw).hexdigest() == item['raw_sha256']
    source = raw.decode(); result = {}
    for role, length in [('EXTERNAL_INITIAL',128),('INTERNAL',30),('EXTERNAL_FINAL',128)]:
        match = re.search(r'pub const BABYBEAR_POSEIDON2_RC_32_'+role+r'\b.*?=\s*BabyBear::new_(?:2d_)?array\((.*?)\);', source, re.S)
        assert match, role
        values = [int(x,16) for x in re.findall(r'0x[0-9a-fA-F]+', match.group(1))]
        assert len(values)==length and all(0<=x<P for x in values)
        result[role] = values if role=='INTERNAL' else [values[i:i+32] for i in range(0,128,32)]
    return result


def external(state):
    matrix = [(2,3,1,1),(1,2,3,1),(1,1,2,3),(3,1,1,2)]
    block = [add(M(C(c), state[j+k]) for k,c in enumerate(row))
             for j in range(0,32,4) for row in matrix]
    totals = [add(block[i::4]) for i in range(4)]
    return [A(x,totals[i%4]) for i,x in enumerate(block)]


def internal(state):
    inv2 = pow(2,P-2,P)
    diagonal = [-2,1,2,inv2,3,4,-inv2,-3,-4]
    diagonal += [pow(inv2,k,P) for k in (8,2,3,4,5,6,7,9,10,12,27)]
    diagonal += [-pow(inv2,k,P) for k in (8,2,3,4,5,6,7,9,10,12,14,27)]
    assert len(diagonal)==32
    total=add(state)
    return [A(total,M(C(d),x)) for d,x in zip(diagonal,state)]


def compile_permutation(log_rows=1):
    assert type(log_rows) is int and 1<=log_rows<=25
    rc=constants(); assignments=[]; rounds=[]; next_column=32
    def assign(e):
        nonlocal next_column
        column=next_column;next_column+=1;assignments.append(e)
        return V(column)
    def sbox(x):
        x2=assign(M(x,x));x3=assign(M(x2,x));x6=assign(M(x3,x3))
        return M(x6,x)
    state=external([V(i) for i in range(32)])
    for phase,constants_ in [('initial',rc['EXTERNAL_INITIAL']),('internal',rc['INTERNAL']),('final',rc['EXTERNAL_FINAL'])]:
        for index,constant in enumerate(constants_):
            first=next_column
            if phase=='internal':
                nonlinear=[sbox(A(state[0],C(constant))),*state[1:]]
                transformed=internal(nonlinear)
            else:
                nonlinear=[sbox(A(x,C(c))) for x,c in zip(state,constant)]
                transformed=external(nonlinear)
            state=[assign(x) for x in transformed]
            rounds.append(dict(phase=phase,round=index,first_column=first,
                               end_column=next_column,output_columns=[x[1] for x in state]))
    assert next_column==2106 and len(assignments)==2074
    constraints=[S(V(i+32),e) for i,e in enumerate(assignments)]
    table=dict(width=next_column,maxLog=log_rows,constraints=constraints,interactions=[])
    return dict(table=table,assignments=assignments,input_columns=list(range(32)),
                output_columns=[x[1] for x in state],rounds=rounds)


def evaluate(e,row):
    op=e[0]
    if op=='c':return e[1]
    if op=='v':
        assert e[2]==0
        return row[e[1]]
    if op=='-':return -evaluate(e[1],row)%P
    a,b=evaluate(e[1],row),evaluate(e[2],row)
    if op=='+':return (a+b)%P
    assert op=='*'
    return a*b%P


def witness(compiled,inputs):
    assert len(inputs)==32 and all(type(x)is int and 0<=x<P for x in inputs)
    row=list(inputs)
    for assignment in compiled['assignments']:
        row.append(evaluate(assignment,row))
    return row
