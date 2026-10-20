"""Same auxiliary witness using base-field source evaluation and cached powers.
Only generation on canonical base traces; never extension-point verification.
"""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'generic-air'))
import pq384_ext8_auxiliary as reference
import pq384_ext8_reference as f
from reference import expr_degree


def compile_program(table,public):
    code=[];memo={}
    def emit(e):
        expr_degree(e,table['width'],max(len(public),max_public(e)+1))
        def key(x):return tuple(key(y) if isinstance(y,list) else y for y in x)
        k=key(e)
        if k in memo:return memo[k]
        op=e[0]
        if op=='c':node=('c',e[1]%f.P)
        elif op=='p':node=('c',public[e[1]] if e[1]<len(public) else 0)
        elif op=='v':node=('n' if e[2] else 'v',e[1])
        elif op in ('first','last','trans'):node=(op,)
        elif op=='-':node=('-',emit(e[1]))
        else:node=(op,emit(e[1]),emit(e[2]))
        memo[k]=len(code);code.append(node);return memo[k]
    def max_public(e):
        return e[1] if e[0]=='p' else max([max_public(x) for x in e[1:] if isinstance(x,list)],default=-1)
    groups=[([emit(e) for e in i['msg']],[emit(e) for e in i['mult']],i['bus']) for i in table['interactions']]
    return code,groups


def generate(table,rows,public,alpha,gamma):
    shape=reference.layout(table)
    reference.require(isinstance(rows,list) and len(rows)>=2 and len(rows)&(len(rows)-1)==0,'power-of-two rows')
    reference.require(all(len(row)==table['width'] and all(type(x)is int and 0<=x<f.P for x in row) for row in rows),'canonical source rows')
    reference.require(all(type(x)is int and 0<=x<f.P for x in public) and reference.canonical(alpha) and reference.canonical(gamma),'canonical public/challenges')
    code,groups=compile_program(table,public)
    max_len=max((len(msg) for msg,_,_ in groups),default=0)
    powers=[f.ONE]
    for _ in range(max_len):powers.append(f.mul(powers[-1],alpha))
    tags=[f.scale(powers[len(msg)],bus+1) for msg,_,bus in groups]
    accumulators=[f.ONE]*len(shape['order']);aux_rows=[]
    for r,row in enumerate(rows):
        nxt=rows[(r+1)%len(rows)];values=[]
        for ins in code:
            op=ins[0]
            if op=='c':value=ins[1]
            elif op=='v':value=row[ins[1]]
            elif op=='n':value=nxt[ins[1]]
            elif op=='first':value=int(r==0)
            elif op=='last':value=int(r+1==len(rows))
            elif op=='trans':value=int(r+1!=len(rows))
            elif op=='-':value=-values[ins[1]]%f.P
            elif op=='+':value=(values[ins[1]]+values[ins[2]])%f.P
            elif op=='*':value=values[ins[1]]*values[ins[2]]%f.P
            else:raise ValueError('opcode')
            values.append(value)
        chains=[];factors=[]
        for (msg,bits,_),tag in zip(groups,tags):
            fingerprint=tag
            for i,reg in enumerate(msg):fingerprint=f.add(fingerprint,f.scale(powers[i],values[reg]))
            p=f.sub(gamma,fingerprint)
            if not bits:factors.append(f.ONE);continue
            value=f.add(f.ONE,f.scale(f.sub(p,f.ONE),values[bits[0]]));ps=[];pis=[]
            for reg in bits[1:]:
                p=f.mul(p,p);ps.append(p)
                value=f.mul(value,f.add(f.ONE,f.scale(f.sub(p,f.ONE),values[reg])));pis.append(value)
            chains.extend(ps+pis);factors.append(value)
        aux_rows.append(chains+accumulators.copy())
        accumulators=[f.mul(a,factors[i]) for a,i in zip(accumulators,shape['order'])]
    return dict(aux_rows=aux_rows,finals=accumulators)
