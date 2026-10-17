"""Constrained fixed nibble truth tables in canonical np-air-v1.
Lookup requests are not yet connected to SHA phase rows. No proof/security claim.
"""
from collections import Counter
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent/'generic-air'))
import reference as ref
import sha384_nibble_circuit as circuit

OPS = ('xor3', 'choose', 'majority', 'splice1', 'splice2', 'splice3')
C = lambda x: ['c', x]
V = lambda x, nxt=0: ['v', x, nxt]
A = lambda x,y: ['+',x,y]
M = lambda x,y: ['*',x,y]
N = lambda x: ['-',x]
S = lambda x,y: A(x,N(y))


def add(xs):
    out = C(0)
    for x in xs: out=A(out,x)
    return out

def word(bits):return add([M(C(1 << i), x) for i,x in enumerate(bits)])
def xor(x,y):return S(A(x,y),M(C(2),M(x,y)))
def bit(x):return M(x,S(x,C(1)))


def fixed_table(op, multiplicity_bits):
    assert 1 <= multiplicity_bits <= 25
    n = 4 if op == 'range' else 8 if op.startswith('splice') else 12
    bs = [V(i) for i in range(n)]; width=n+multiplicity_bits
    # Binary row index enumerates the full table. First/last endpoints and a
    # nonwrapping transition also rule out shorter power-of-two traces.
    constraints=[bit(V(i)) for i in range(width)]
    constraints += [M(['first'], x) for x in bs]
    constraints += [M(['last'], S(x,C(1))) for x in bs]
    constraints += [M(['trans'], S(word([V(i,1) for i in range(n)]), A(word(bs),C(1))))]
    if op == 'range': msg=[word(bs)];bus=1
    else:
        x,y,z=bs[:4],bs[4:8],bs[8:12]
        if op == 'xor3': out=[xor(xor(a,b),c) for a,b,c in zip(x,y,z)]
        elif op == 'choose':out=[A(M(a,b),M(S(C(1),a),c)) for a,b,c in zip(x,y,z)]
        elif op == 'majority':out=[S(add([M(a,b),M(a,c),M(b,c)]),M(C(2),M(M(a,b),c))) for a,b,c in zip(x,y,z)]
        else:
            shift=int(op[-1]);out=(x+y)[shift:shift+4]
        msg=[C(OPS.index(op)),word(x),word(y),word(z) if z else C(0),word(out)];bus=0
    return dict(width=width,maxLog=n,constraints=constraints,
        interactions=[dict(bus=bus,send=False,mult=[V(n+i) for i in range(multiplicity_bits)],msg=msg)])


def table_rows(op, counts, multiplicity_bits):
    n=4 if op == 'range' else 8 if op.startswith('splice') else 12
    rows=[]
    for index in range(1 << n):
        args=tuple((index >> (4*i)) & 15 for i in range(n//4))
        key=args if op == 'range' else (OPS.index(op), *args, *([0] if len(args)==2 else []), circuit.relation(op,args))
        count=counts[key]; assert 0 <= count < 1 << multiplicity_bits
        rows.append([(index >> i)&1 for i in range(n)]+[(count >> i)&1 for i in range(multiplicity_bits)])
    return rows


def request_table(messages, bus):
    width=1+len(messages[0]);active=V(0)
    table=dict(width=width,maxLog=max(1,(len(messages)-1).bit_length()),
        constraints=[bit(active)]+[M(S(C(1),active),V(i)) for i in range(1,width)],
        interactions=[dict(bus=bus,send=True,mult=[active],msg=[V(i) for i in range(1,width)])])
    rows=[[1,*message] for message in messages]
    rows += [[0]*width for _ in range((1 << table['maxLog'])-len(rows))]
    return table,rows


def fixture(multiplicity_bits=21):
    import plan_sha384_nibble_rows as planner
    g=circuit.compile_graph();source=[i%16 for i in range(384)];values=circuit.witness(g,source)
    requests={op:[] for op in OPS}
    for op,ins,outs,_ in g.gates:
        if op in OPS:
            args=[values[w] for w in ins]
            requests[op].append((OPS.index(op),*args,*([0] if len(args)==2 else []),values[outs[0]]))
    missing=planner.plan(g)[2]
    requests['range']=[(values[w],) for w in sorted(missing)]
    tables=[];traces=[];names=[]
    for op,messages in requests.items():
        counts=Counter(messages)
        tables.append(fixed_table(op,multiplicity_bits));traces.append(table_rows(op,counts,multiplicity_bits));names.append(op+'/fixed')
        table,rows=request_table(messages,1 if op=='range' else 0)
        tables.append(table);traces.append(rows);names.append(op+'/requests')
    air=dict(format='np-air-v1',numBuses=2,numPub=0,tables=tables)
    ref.schema(air)
    return air,traces,names,requests
