#!/usr/bin/env python3
"""Independent variable-row WHIR verifier, diagnostic profile only.

Supports 2^n rows for n=3..8, positive width, folds[1,1], LDE4, cap1,
eight queries per round, no grinding, full-round BLAKE2s. No witness input.
Not formally verified; no cryptographic security-level claim.
The caller must derive the transcript and point from a verified prior stage.
"""
import struct
from verify_whir_toy import (P,ZERO,ONE,INV_R,add,sub,mul,base,scale,eq,poly,
    raw,ext,words,digest,root,require,merkle,tree_index,SCHEDULE,Transcript)


def draw_queries(transcript,nonce,bits):
    """Pinned transcript_utils::draw_query_bits + LE BitSource.

    Randomness draws pad (ceil(querybits/32)+1) words to eight-word blocks.
    The first word is reserved for PoW even with a zero PoW target.
    """
    require(type(nonce)is int and 0<=nonce<2**64,'nonce')
    require(type(bits)is int and 1<=bits<=9,'query bit width')
    transcript.seed=digest(transcript.seed+struct.pack('<Q',nonce))
    required_words=(8*bits+31)//32
    padded=((required_words+1+7)//8)*8
    source=[]
    for block in range(padded//8):
        if block:transcript.seed=digest(transcript.seed)
        source.extend(struct.unpack('<8I',transcript.seed))
    stream=sum(w<<(32*i) for i,w in enumerate(source[1:]))
    return [(stream>>(bits*i))&((1<<bits)-1) for i in range(8)]


def monomial_tensor_eval(coefficients,point):
    require(len(coefficients)==2**len(point),'monomial tensor shape')
    values=list(coefficients)
    for x in point:
        values=[add(values[j],mul(x,values[j+1])) for j in range(0,len(values),2)]
    return values[0]


def verify_with_handoff(x,expected_root,handoff,width,log_rows):
    require(type(log_rows)is int and 3<=log_rows<=8,'supported row dimension')
    require(isinstance(expected_root,list) and len(expected_root)==8 and
            all(type(v)is int and 0<=v<2**32 for v in expected_root),'root encoding')
    require(type(width)is int and width>0,'expected column width')
    p=x['proof'];require(p['whir_schedule']==SCHEDULE,'unsupported schedule')
    wit=p['witness_commitment'];require(wit['num_columns']==width and len(wit['evals'])==width,'column shape')
    require(wit['commitment']['cap']['cap']==[expected_root],'root binding')
    for name in ('memory_commitment','setup_commitment'):
        a=p[name];require(a['num_columns']==0 and a['evals']==[] and a['queries']==[] and a['commitment']['cap']['cap']==[],'unexpected auxiliary oracle')
    require(isinstance(handoff,tuple) and len(handoff)==2,'verified protocol handoff')
    t,z=handoff
    require(len(z)==log_rows,'point dimension')

    require([ext(v) for v in x['evaluation_point']]==z,'point draw')
    require([ext(v) for v in p['original_evaluation_point']]==z,'point binding')
    t.commit_ext(wit['evals']);batch=t.draw(1,True)[0]
    require(ext(p['batching_challenge'])==batch,'batch draw')
    require(words(x['initial_whir_seed'])==t.seed,'initial seed')
    claim=ZERO;power=ONE
    for v in wit['evals']:claim=add(claim,mul(power,ext(v)));power=mul(power,batch)
    require(ext(p['batched_opening'])==claim,'batch claim')
    require(len(p['sumcheck_polys'])==2 and all(len(c)==3 for c in p['sumcheck_polys']),'sumcheck shape')
    require(len(p['ood_samples'])==1 and len(p['pow_nonces'])==2,'round shape')
    require(len(p['intermediate_whir_oracles'])==1,'oracle shape')
    def sumcheck(i,claim):
        enc=p['sumcheck_polys'][i];cs=[ext(c) for c in enc]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'sumcheck identity')
        t.commit_ext(enc);r=t.draw(1)[0]
        return r,poly(cs,r)
    r0,claim=sumcheck(0,claim)
    mid=p['intermediate_whir_oracles'][0];caps=mid['commitment']['cap']['cap']
    require(len(caps)==1 and len(caps[0])==8,'intermediate cap');t.commit(caps[0])
    ood=t.draw(1)[0];oodvalue=ext(p['ood_samples'][0]);t.commit_ext(p['ood_samples'])
    indices=draw_queries(t,p['pow_nonces'][0],log_rows+1);gamma=t.draw(1,True)[0]
    claim=add(claim,mul(gamma,oodvalue));power=mul(gamma,gamma)
    terms=[(ood,gamma)]
    require(len(wit['queries'])==8,'base query count')
    for index,q in zip(indices,wit['queries']):
        require(q['index']==tree_index(index,log_rows),'base query index')
        values=q['leaf_values_concatenated'];require(len(values)==2*width,'base leaf width')
        require(all(type(v)is int and 0<=v<P for v in values),'base leaf field')
        merkle([values[o*width+c] for c in range(width) for o in range(2)],q['index'],q['path'],expected_root,log_rows+1)
        ys=[]
        for o in range(2):
            acc=ZERO;b=ONE
            for v in values[o*width:(o+1)*width]:acc=add(acc,scale(b,v*INV_R%P));b=mul(b,batch)
            ys.append(acc)
        # Recover even/odd univariate parts from evaluations at t,-t.
        inv=pow(pow(root(log_rows+2),index,P),-1,P)
        folded=add(scale(add(*ys),pow(2,-1,P)),mul(r0,scale(sub(*ys),inv*pow(2,-1,P)%P)))
        point=base(pow(root(log_rows+1),index,P));terms.append((point,power))
        claim=add(claim,mul(power,folded));power=mul(power,gamma)
    r1,claim=sumcheck(1,claim)
    final=p['final_monomials'];require(len(final)==2**(log_rows-2),'final polynomial degree')
    cs=[ext(c) for c in final];t.commit_ext(final)
    indices=draw_queries(t,p['pow_nonces'][1],log_rows)
    require(len(mid['queries'])==8,'final query count')
    for index,q in zip(indices,mid['queries']):
        require(q['index']==tree_index(index,log_rows-1),'final query index')
        es=q['leaf_values_concatenated'];require(len(es)==2,'intermediate leaf width')
        merkle([w for e in es for w in raw(e)],q['index'],q['path'],caps[0],log_rows)
        folded=add(ext(es[0]),mul(r1,ext(es[1])))
        require(folded==poly(cs,base(pow(root(log_rows),index,P))),'final query fold')
    # Monomial tensor coefficients are not univariate evaluations at a bit index.
    total=ZERO
    for index in range(2**(log_rows-2)):
        bits=[base((index>>j)&1) for j in range(log_rows-2)]
        weight=mul(eq(z[0],r0),eq(z[1],r1))
        for zj,b in zip(z[2:],bits):weight=mul(weight,eq(zj,b))
        for point,power in terms:
            extra=mul(power,eq(point,r1));coordinate=mul(point,point)
            for b in bits:
                extra=mul(extra,eq(coordinate,b));coordinate=mul(coordinate,coordinate)
            weight=add(weight,extra)
        total=add(total,mul(monomial_tensor_eval(cs,bits),weight))
    require(total==claim,'final sumcheck')
    return True
