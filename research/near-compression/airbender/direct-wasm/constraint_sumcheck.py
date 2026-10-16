#!/usr/bin/env python3
"""Fixed eight-row constraint zerocheck + WHIR experiment. No security claim.

Verifier inputs: trusted constraint specification, expected commitment root, proof.
Neither the witness nor a prover-supplied transcript state is a verifier input.
"""
import hashlib, itertools, json, struct
from verify_whir_toy import (P,ZERO,ONE,add,sub,mul,base,scale,eq,poly,ext,
                            require,Transcript,_verify_with_handoff)
from check_whir_handoff import mle

def encode(e):
    v=[e[i]*2**32%P for i in (0,2,1,3)]
    return {'c0':{'c0':v[0],'c1':v[1]},'c1':{'c0':v[2],'c1':v[3]}}

def specification(export,public_instructions=None):
    spec={k:export[k] for k in ('columns','constraints','field_modulus')}
    if public_instructions is not None:spec['public_instructions']=public_instructions
    return spec

def public_limbs(spec):
    instructions=spec['public_instructions']
    require(isinstance(instructions,list) and len(instructions)==8,'public instruction count')
    require(all(isinstance(r,list) and len(r)==3 and
                all(type(v)is int and 0<=v<2**32 for v in r) for r in instructions),'public instruction encoding')
    return [[limb for v in row for limb in (v%65536,v//65536)] for row in instructions]

def degree(e):
    require(isinstance(e,dict) and len(e)==1,'expression shape')
    op,a=next(iter(e.items()))
    if op=='const':
        require(type(a)is int and a>=0,'constant');return 0
    if op=='col':
        require(type(a)is int and 0<=a<104,'column');return 1
    if op=='neg':return degree(a)
    require(op in ('add','mul') and isinstance(a,list) and len(a)==2,'operator')
    ds=[degree(v) for v in a]
    return max(ds) if op=='add' else sum(ds)

def statement(spec,root):
    require(spec['columns']==104 and spec['field_modulus']==P and len(spec['constraints'])==106,'spec shape')
    require(all(degree(e)<=2 for e in spec['constraints']),'constraint degree')
    require(len(root)==8 and all(type(v)is int and 0<=v<2**32 for v in root),'root encoding')
    if 'public_instructions' in spec:public_limbs(spec)
    h=hashlib.sha256(json.dumps(spec,sort_keys=True,separators=(',',':')).encode()).digest()
    domain=b'NEAR-WASM-PUBLIC-CONSTRAINT-WHIR-EXPERIMENT-V2' if 'public_instructions' in spec else b'NEAR-WASM-CONSTRAINT-WHIR-EXPERIMENT-V1'
    return list(domain)+list(struct.unpack('<8I',h))+[8,104,106,3,4,1,1,2,1,1,8,8,4,0,0]+root

def evaluate(e,row):
    op,a=next(iter(e.items()))
    if op=='const':return base(a)
    if op=='col':return row[a]
    if op=='neg':return sub(ZERO,evaluate(a,row))
    return (add if op=='add' else mul)(evaluate(a[0],row),evaluate(a[1],row))

def batched(spec,row,alpha):
    out=ZERO;power=ONE
    for e in spec['constraints']:
        out=add(out,mul(power,evaluate(e,row)));power=mul(power,alpha)
    return out

def weighted(spec,row,alpha,tau,point):
    out=batched(spec,row,alpha)
    if 'public_instructions' in spec:
        limbs=public_limbs(spec);power=ONE
        for _ in spec['constraints']:power=mul(power,alpha)
        for c in range(6):
            expected=mle([r[c] for r in limbs],point)
            out=add(out,mul(power,sub(row[c],expected)));power=mul(power,alpha)
    for t,r in zip(tau,point):out=mul(out,eq(t,r))
    return out

def begin(spec,root):
    words=statement(spec,root);t=Transcript(words)
    alpha=t.draw(1,True)[0];tau=t.draw(3,True)
    return words,t,alpha,tau

def interpolate(values):
    # Four distinct base-field nodes, degree at most three.
    out=[ZERO]*4
    for i,y in enumerate(values):
        cs=[1];den=1
        for j in range(4):
            if i==j:continue
            nxt=[0]*(len(cs)+1)
            for k,c in enumerate(cs):nxt[k]=(nxt[k]-j*c)%P;nxt[k+1]=(nxt[k+1]+c)%P
            cs=nxt;den=den*(i-j)%P
        for k,c in enumerate(cs):out[k]=add(out[k],scale(y,c*pow(den,-1,P)%P))
    return out

def prove_sumcheck(spec,root,rows):
    require(len(rows)==8 and all(len(r)==104 for r in rows),'row shape')
    require(all(type(v)is int and 0<=v<P for row in rows for v in row),'witness field')
    words,t,alpha,tau=begin(spec,root);point=[];rounds=[]
    for i in range(3):
        values=[]
        for node in range(4):
            total=ZERO
            for suffix in itertools.product((ZERO,ONE),repeat=2-i):
                at=point+[base(node)]+list(suffix)
                row=[mle([r[c] for r in rows],at) for c in range(104)]
                total=add(total,weighted(spec,row,alpha,tau,at))
            values.append(total)
        encoded=[encode(c) for c in interpolate(values)];rounds.append(encoded)
        t.commit_ext(encoded);point.append(t.draw(1,True)[0])
    return rounds,{'root':root,'statement_words':words,'pre_opening_seed':list(struct.unpack('<8I',t.seed)),
                   'evaluation_point':[encode(r) for r in point]}

def verify(proof,spec,root):
    words,t,alpha,tau=begin(spec,root);claim=ZERO;point=[]
    rounds=proof['constraint_sumcheck']
    require(len(rounds)==3,'constraint round count')
    for encoded in rounds:
        require(len(encoded)==4,'constraint polynomial degree')
        cs=[ext(v) for v in encoded]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'constraint sumcheck identity')
        t.commit_ext(encoded);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r)
    opening=proof['opening'];require(opening['statement_words']==words,'constraint statement binding')
    row=[ext(v) for v in opening['proof']['witness_commitment']['evals']]
    require(len(row)==104,'terminal column count')
    require(claim==weighted(spec,row,alpha,tau,point),'terminal constraint evaluation')
    _verify_with_handoff(opening,root,(t,point))
    return True
