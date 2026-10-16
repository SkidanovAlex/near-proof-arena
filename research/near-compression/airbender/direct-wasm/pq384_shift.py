#!/usr/bin/env python3
"""Reduce current/cyclic-next MLE claims to original-column openings.

Generic row dimension/column width algebra; canonical Ext4 word encoding.
Caller supplies the SHA384 transcript. Caller must authenticate final evaluations through a coherent PCS.
No security level or quantum soundness claim.
"""
import itertools
from packed_claim_handoff import canonical_ext as ext

def encode(value):return list(value)
from verify_whir_toy import P,ZERO,ONE,base,add,sub,mul,scale,eq,poly,require
from check_whir_handoff import mle

def eq_point(a,b):
    require(len(a)==len(b),'point dimensions');out=ONE
    for x,y in zip(a,b):out=mul(out,eq(x,y))
    return out

def shift_kernel(point,x):
    """MLE_x(eq(point, Boolean index x minus one modulo 2^n)).

Subtract-one borrow automaton. The final borrow is dropped for cyclic indexing.
Evaluation is O(n), with no table/witness access.
"""
    require(len(point)==len(x),'shift dimensions')
    no_borrow=ZERO;borrow=ONE
    for r,y in zip(point,x):
        no_borrow,borrow=(add(mul(no_borrow,eq(r,y)),mul(borrow,mul(y,sub(ONE,r)))),
                          mul(borrow,mul(sub(ONE,y),r)))
    return add(no_borrow,borrow)

def power(x,n):
    out=ONE
    for _ in range(n):out=mul(out,x)
    return out

def batch(values,alpha):
    out=ZERO;p=ONE
    for v in values:out=add(out,mul(p,v));p=mul(p,alpha)
    return out

def kernel(point,x,alpha,width):
    return add(eq_point(point,x),mul(power(alpha,width),shift_kernel(point,x)))

def interpolate(values):
    out=[ZERO]*len(values)
    for i,y in enumerate(values):
        cs=[1];den=1
        for j in range(len(values)):
            if i==j:continue
            nxt=[0]*(len(cs)+1)
            for k,c in enumerate(cs):nxt[k]=(nxt[k]-j*c)%P;nxt[k+1]=(nxt[k+1]+c)%P
            cs=nxt;den=den*(i-j)%P
        for k,c in enumerate(cs):out[k]=add(out[k],scale(y,c*pow(den,-1,P)%P))
    return out

def start_claim(proof,point,width,t):
    require(type(width)is int and width>0 and len(point)>0,'reduction shape')
    curr=proof['current_evals'];nxt=proof['next_evals']
    require(len(curr)==len(nxt)==width,'claim width')
    # Current and next share the same source-column batching challenge.
    t.commit_ext(curr+nxt);alpha=t.draw(1,True)[0]
    return alpha,batch([ext(v) for v in curr+nxt],alpha)

def prove(rows,point,t):
    n=len(point);width=len(rows[0]);require(n>0 and len(rows)==2**n,'row count')
    require(width>0 and all(len(row)==width and all(type(v)is int and 0<=v<P for v in row) for row in rows),'rows')
    current=[mle([row[c] for row in rows],point) for c in range(width)]
    shifted=rows[1:]+rows[:1]
    nxt=[mle([row[c] for row in shifted],point) for c in range(width)]
    proof={'current_evals':[encode(v) for v in current],'next_evals':[encode(v) for v in nxt],'rounds':[]}
    alpha,claim=start_claim(proof,point,width,t);at=[]
    for i in range(n):
        vals=[]
        for node in range(3):
            total=ZERO
            for suffix in itertools.product((ZERO,ONE),repeat=n-i-1):
                x=at+[base(node)]+list(suffix)
                w=batch([mle([row[c] for row in rows],x) for c in range(width)],alpha)
                total=add(total,mul(kernel(point,x,alpha,width),w))
            vals.append(total)
        cs=interpolate(vals)
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'honest shift identity')
        encoded=[encode(v) for v in cs];proof['rounds'].append(encoded);t.commit_ext(encoded)
        r=t.draw(1,True)[0];at.append(r);claim=poly(cs,r)
    final=[mle([row[c] for row in rows],at) for c in range(width)]
    require(claim==mul(kernel(point,at,alpha,width),batch(final,alpha)),'honest final shift claim')
    return proof,at,final

def verify(proof,point,width,t,final_evals):
    """Return PCS point; caller must authenticate final_evals there using t.

This function alone is only an algebraic reduction, never a proof verifier.
"""
    alpha,claim=start_claim(proof,point,width,t)
    require(len(proof['rounds'])==len(point),'shift round count');at=[]
    for encoded in proof['rounds']:
        require(len(encoded)==3,'shift round degree');cs=[ext(v) for v in encoded]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'shift sumcheck identity')
        t.commit_ext(encoded);r=t.draw(1,True)[0];at.append(r);claim=poly(cs,r)
    require(len(final_evals)==width,'final opening width')
    require(claim==mul(kernel(point,at,alpha,width),batch([ext(v) for v in final_evals],alpha)),
            'shift terminal opening')
    return at
