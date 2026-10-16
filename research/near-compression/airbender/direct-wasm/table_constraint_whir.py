#!/usr/bin/env python3
"""Canonical AIR table-local zerocheck -> cyclic-next reduction -> WHIR.

Fixed eight-row WHIR profile, arbitrary nonempty column width, source degree
through16. Trusted spec/root are verifier inputs; private rows never are.
Does not prove cross-table/public buses, full HoldsP or quantum security.
"""
import hashlib,itertools,json,struct,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'generic-air'))
from reference import schema,expr_degree
from verify_whir_toy import (P,ZERO,ONE,base,add,sub,mul,eq,poly,ext,require,Transcript,_verify_with_handoff)
from constraint_sumcheck import encode
from check_whir_handoff import mle
import shift_opening as shift

def specification(fixture):
    return {'air':fixture['air'],'table_index':fixture['table_index'],'public':fixture['public'],'log_rows':3}

def validate(spec):
    air=spec['air'];schema(air);i=spec['table_index']
    require(type(i)is int and 0<=i<len(air['tables']),'table index')
    table=air['tables'][i];require(spec['log_rows']==3 and table['maxLog']>=3,'table row profile')
    require(type(table['width'])is int and table['width']>0,'nonempty table')
    require(isinstance(spec['public'],list) and all(type(v)is int and 0<=v<P for v in spec['public']),'public field')
    degree=max([expr_degree(e,table['width'],air['numPub']) for e in table['constraints']],default=0)
    require(degree<=16,'supported source degree')
    return table,degree

def statement(spec,root):
    table,degree=validate(spec)
    require(len(root)==8 and all(type(v)is int and 0<=v<2**32 for v in root),'root encoding')
    h=hashlib.sha256(json.dumps(spec,sort_keys=True,separators=(',',':')).encode()).digest()
    return list(b'NEAR-GENERIC-AIR-TABLE-WHIR-EXPERIMENT-V1')+list(struct.unpack('<8I',h))+[
        8,table['width'],degree,4,1,1,2,1,1,8,8,4,0,0]+root

def begin(spec,root):
    words=statement(spec,root);t=Transcript(words)
    alpha=t.draw(1,True)[0];tau=t.draw(3,True)
    return words,t,alpha,tau

def selectors(point):
    first=ONE;last=ONE
    for r in point:first=mul(first,sub(ONE,r));last=mul(last,r)
    return {'first':first,'last':last,'trans':sub(ONE,last)}

def evaluate(e,current,nxt,public,sels):
    op=e[0]
    if op=='c':return base(e[1])
    if op=='v':return (nxt if e[2] else current)[e[1]]
    if op=='p':return base(public[e[1]] if e[1]<len(public) else 0)
    if op in sels:return sels[op]
    a=evaluate(e[1],current,nxt,public,sels)
    if op=='-':return sub(ZERO,a)
    b=evaluate(e[2],current,nxt,public,sels)
    return (add if op=='+' else mul)(a,b)

def weighted(spec,alpha,tau,point,current,nxt):
    table=spec['air']['tables'][spec['table_index']];sels=selectors(point)
    total=ZERO;power=ONE
    for e in table['constraints']:
        total=add(total,mul(power,evaluate(e,current,nxt,spec['public'],sels)));power=mul(power,alpha)
    return mul(shift.eq_point(tau,point),total)

def prove(spec,root,rows):
    table,degree=validate(spec);width=table['width']
    require(len(rows)==8 and all(len(row)==width and all(type(v)is int and 0<=v<P for v in row) for row in rows),'witness shape')
    words,t,alpha,tau=begin(spec,root);rounds=[];point=[];nextrows=rows[1:]+rows[:1]
    for i in range(3):
        values=[]
        for node in range(degree+2):
            total=ZERO
            for suffix in itertools.product((ZERO,ONE),repeat=2-i):
                at=point+[base(node)]+list(suffix)
                curr=[mle([row[c] for row in rows],at) for c in range(width)]
                nxt=[mle([row[c] for row in nextrows],at) for c in range(width)]
                total=add(total,weighted(spec,alpha,tau,at,curr,nxt))
            values.append(total)
        cs=[encode(v) for v in shift.interpolate(values)];rounds.append(cs)
        t.commit_ext(cs);point.append(t.draw(1,True)[0])
    # Same transcript; shift reduction commits the current/next terminal claims.
    reduction,at,final=shift.prove(rows,point,t)
    partial={'constraint_rounds':rounds,'shift_reduction':reduction}
    handoff={'root':root,'statement_words':words,'pre_opening_seed':list(struct.unpack('<8I',t.seed)),
             'evaluation_point':[encode(v) for v in at]}
    return partial,handoff

def verify(proof,spec,root):
    table,degree=validate(spec);words,t,alpha,tau=begin(spec,root)
    rounds=proof['constraint_rounds'];require(len(rounds)==3,'constraint round count')
    point=[];claim=ZERO
    for encoded in rounds:
        require(len(encoded)==degree+2,'constraint round degree');cs=[ext(v) for v in encoded]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'table zerocheck identity')
        t.commit_ext(encoded);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r)
    reduction=proof['shift_reduction'];width=table['width']
    require(len(reduction['current_evals'])==len(reduction['next_evals'])==width,'terminal columns')
    curr=[ext(v) for v in reduction['current_evals']];nxt=[ext(v) for v in reduction['next_evals']]
    require(claim==weighted(spec,alpha,tau,point,curr,nxt),'table terminal constraint')
    opening=proof['opening'];require(opening['statement_words']==words,'table statement binding')
    final=opening['proof']['witness_commitment']['evals']
    at=shift.verify(reduction,point,width,t,final)
    _verify_with_handoff(opening,root,(t,at),width=width)
    return True
