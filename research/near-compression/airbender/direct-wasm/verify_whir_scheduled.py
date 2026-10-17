#!/usr/bin/env python3
"""Independent dimension-derived WHIR diagnostic, 2..8192 rows.

Full-round BLAKE2s, LDE4, cap1, eight queries per round, no grinding.
Repeated one-variable folds leave at most two final coefficients. Two-row
tables use explicit full-row disclosure with complete RS/Merkle recomputation.
No external witness input, security-level claim, formal verification or production readiness.
Caller must derive the handoff transcript and point from a verified protocol.
"""
import struct
from verify_whir_toy import (P,ZERO,ONE,INV_R,add,sub,mul,base,scale,eq,poly,
    raw,ext,words,digest,root,require,merkle,Transcript)


def schedule(log_rows):
    require(type(log_rows)is int and 1<=log_rows<=13,'supported row dimension')
    folds=[] if log_rows==1 else [1]*max(2,log_rows-1)
    return {'base_lde_factor':4,'cap_size':1,'whir_steps_schedule':folds,
            'whir_queries_schedule':[8]*len(folds),'whir_steps_lde_factors':[4]*(len(folds)-1),
            'whir_pow_schedule':[0]*len(folds)}


def draw_queries(t,nonce,bits):
    require(type(nonce)is int and 0<=nonce<2**64,'nonce')
    require(type(bits)is int and 1<=bits<=15,'query width')
    t.seed=digest(t.seed+struct.pack('<Q',nonce))
    padded=(((8*bits+31)//32+1+7)//8)*8
    source=[]
    for block in range(padded//8):
        if block:t.seed=digest(t.seed)
        source.extend(struct.unpack('<8I',t.seed))
    stream=sum(w<<(32*i) for i,w in enumerate(source[1:]))
    return [(stream>>(bits*i))&((1<<bits)-1) for i in range(8)]


def tensor_eval(coefficients,point):
    require(len(coefficients)==2**len(point),'tensor shape')
    values=list(coefficients)
    for x in point:
        values=[add(values[j],mul(x,values[j+1])) for j in range(0,len(values),2)]
    return values[0]


def tree_index(query,remaining,folds):
    coset=query%4
    return (((coset&1)<<1)|(coset>>1))*2**(remaining-folds)+query//4


def cap_check(cap):
    require(isinstance(cap,list) and len(cap)==8 and
            all(type(w)is int and 0<=w<2**32 for w in cap),'cap encoding')


def verify_with_handoff(x,expected_root,handoff,width,log_rows):
    expected_schedule=schedule(log_rows)
    require(type(width)is int and width>0,'column width');cap_check(expected_root)
    if log_rows==1:return verify_two_row(x,expected_root,handoff,width)
    require(x.get('format')=='scheduled-whir-v1','WHIR format')
    p=x['proof'];require(p['whir_schedule']==expected_schedule,'schedule binding')
    wit=p['witness_commitment']
    require(wit['num_columns']==width and len(wit['evals'])==width,'column shape')
    require(wit['commitment']['cap']['cap']==[expected_root],'root binding')
    for name in ('memory_commitment','setup_commitment'):
        a=p[name]
        require(a['num_columns']==0 and a['evals']==[] and a['queries']==[] and
                a['commitment']['cap']['cap']==[],'unexpected auxiliary oracle')
    require(isinstance(handoff,tuple) and len(handoff)==2,'verified protocol handoff')
    t,z=handoff;require(len(z)==log_rows,'point dimension')
    require([ext(v) for v in x['evaluation_point']]==z,'point draw')
    require([ext(v) for v in p['original_evaluation_point']]==z,'point binding')
    t.commit_ext(wit['evals']);batch=t.draw(1,True)[0]
    require(ext(p['batching_challenge'])==batch,'batch draw')
    require(words(x['initial_whir_seed'])==t.seed,'initial seed')
    claim=ZERO;power=ONE
    for v in wit['evals']:
        claim=add(claim,mul(power,ext(v)));power=mul(power,batch)
    require(ext(p['batched_opening'])==claim,'batch claim')
    folds=expected_schedule['whir_steps_schedule'];rounds=len(folds)
    require(len(p['sumcheck_polys'])==sum(folds) and
            all(len(c)==3 for c in p['sumcheck_polys']),'sumcheck shape')
    require(len(p['ood_samples'])==rounds-1 and len(p['pow_nonces'])==rounds,'round shape')
    mids=p['intermediate_whir_oracles'];require(len(mids)==rounds-1,'oracle count')
    challenges=[];terms=[];remaining=log_rows
    for stage,fold in enumerate(folds):
        before=remaining;fold_challenges=[]
        for _ in range(fold):
            encoded=p['sumcheck_polys'][len(challenges)];cs=[ext(v) for v in encoded]
            require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'sumcheck identity')
            t.commit_ext(encoded);r=t.draw(1)[0];claim=poly(cs,r)
            challenges.append(r);fold_challenges.append(r)
        remaining-=fold;final=stage==rounds-1
        if not final:
            caps=mids[stage]['commitment']['cap']['cap']
            require(len(caps)==1,'intermediate cap count');cap_check(caps[0]);t.commit(caps[0])
            ood=t.draw(1)[0];oodvalue=ext(p['ood_samples'][stage])
            t.commit_ext([p['ood_samples'][stage]])
        else:
            encoded=p['final_monomials'];require(len(encoded)==2**remaining,'final polynomial length')
            final_coefficients=[ext(v) for v in encoded];t.commit_ext(encoded)
        bits=before+2-fold;indices=draw_queries(t,p['pow_nonces'][stage],bits)
        if not final:
            gamma=t.draw(1,True)[0];power=mul(gamma,gamma)
            claim=add(claim,mul(gamma,oodvalue))
            terms.append((len(challenges),ood,gamma))
        oracle=wit if stage==0 else mids[stage-1]
        cap=expected_root if stage==0 else oracle['commitment']['cap']['cap'][0]
        require(len(oracle['queries'])==8,'query count')
        for index,q in zip(indices,oracle['queries']):
            require(q['index']==tree_index(index,before,fold),'query index')
            values=q['leaf_values_concatenated']
            if stage==0:
                require(len(values)==2**fold*width,'base leaf shape')
                require(all(type(v)is int and 0<=v<P for v in values),'base leaf field')
                merkle([values[o*width+c] for c in range(width) for o in range(2**fold)],
                       q['index'],q['path'],cap,bits)
                ys=[]
                for o in range(2**fold):
                    value=ZERO;batch_power=ONE
                    for v in values[o*width:(o+1)*width]:
                        value=add(value,scale(batch_power,v*INV_R%P));batch_power=mul(batch_power,batch)
                    ys.append(value)
                if fold==0:folded=ys[0]
                else:
                    inverse=pow(pow(root(before+2),index,P),-1,P)
                    folded=add(scale(add(*ys),pow(2,-1,P)),
                        mul(fold_challenges[0],scale(sub(*ys),inverse*pow(2,-1,P)%P)))
            else:
                require(len(values)==2**fold,'intermediate leaf shape')
                merkle([w for value in values for w in raw(value)],q['index'],q['path'],cap,bits)
                folded=tensor_eval([ext(v) for v in values],fold_challenges)
            point=base(pow(root(bits),index,P))
            if final:
                require(folded==poly(final_coefficients,point),'final query fold')
            else:
                claim=add(claim,mul(power,folded));terms.append((len(challenges),point,power))
                power=mul(power,gamma)
    total=ZERO
    for index in range(2**remaining):
        tail=[base((index>>j)&1) for j in range(remaining)]
        point=challenges+tail;weight=ONE
        for a,b in zip(z,point):weight=mul(weight,eq(a,b))
        for start,anchor,power in terms:
            extra=power
            for coordinate in point[start:]:
                extra=mul(extra,eq(anchor,coordinate));anchor=mul(anchor,anchor)
            weight=add(weight,extra)
        total=add(total,mul(tensor_eval(final_coefficients,tail),weight))
    require(total==claim,'final sumcheck')
    return True


def verify_two_row(x,expected_root,handoff,width):
    """Caller selects this path only for trusted log_rows=1; no downgrade flag."""
    require(x.get('format')=='direct-two-row-v1','two-row format')
    p=x['proof'];rows=p['rows']
    require(isinstance(rows,list) and len(rows)==2 and
            all(isinstance(r,list) and len(r)==width and all(type(v)is int and 0<=v<P for v in r) for r in rows),
            'two-row witness encoding')
    require(isinstance(handoff,tuple) and len(handoff)==2,'verified handoff')
    t,z=handoff;require(len(z)==1,'two-row point dimension')
    require([ext(v) for v in x['evaluation_point']]==z,'two-row point')
    require(len(p['witness_commitment']['evals'])==width,'two-row claims width')
    claims=[add(base(a),scale(z[0],b-a)) for a,b in zip(*rows)]
    require([ext(v) for v in p['witness_commitment']['evals']]==claims,'two-row evaluations')
    # Commit all eight RS evaluations, arranged as four two-value leaves.
    leaves=[None]*4;montgomery=(2**32)%P
    for q in range(4):
        theta=pow(root(3),q,P);payload=[]
        for a,b in zip(*rows):
            payload.extend([((a+(b-a)*theta)%P)*montgomery%P,
                            ((a-(b-a)*theta)%P)*montgomery%P])
        leaves[tree_index(q,1,1)]=digest(words(payload))
    while len(leaves)>1:leaves=[digest(leaves[i]+leaves[i+1]) for i in range(0,len(leaves),2)]
    require(leaves[0]==words(expected_root),'two-row RS commitment')
    t.commit_ext(p['witness_commitment']['evals']);batch=t.draw(1,True)[0]
    require(ext(p['batching_challenge'])==batch,'two-row batch transcript')
    require(words(x['initial_whir_seed'])==t.seed,'two-row seed')
    return True
