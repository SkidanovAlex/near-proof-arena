"""Distinct-point/heterogeneous-domain joint PCS experiment, no security theorem.

Lift f_j(X) to f_j(X^(D/Dj)); coefficient-table low bits are zero. First quadratic
sumcheck reduces SUM lambda_j<Cj,Wj> to a common Boolean-table MLE point u.
Verifier computes beta_j=lambda_j Wj(u), then one global chain proves the
virtual polynomial SUM beta_j f_j(X^lift) against eq(u,b) weights. No division by
1-u is used. Correlated candidates, adaptive virtual batching, proximity/RBR
and QROM composition are explicit outstanding obligations; Q8 is diagnostic.
"""
from array import array
import json
from pq384_primitives import Transcript,require,hash_parts,u64,P
from packed_claim_handoff import derive_handoff,canonical_ext,vector_bytes
from pq384_one_fold import ZERO,ONE,weights,decode_hash
from pq384_terminal import terminal_context,verify_terminal
from pq384_cached_prover import FlatTree,flat,tuples
from pq384_global_chain import round_start,disclose,sample
from pq384_batched_fold import check_opening
from check_whir_handoff import add,sub,mul
PROFILE='near-pq384-joint-opening-v1'

def power_values(x,count):
    out=[];p=ONE
    for _ in range(count):out.append(p);p=mul(p,x)
    return out

def public(arguments):
    require(isinstance(arguments,list) and 1<=len(arguments)<=128,'joint branch count')
    hs=[];degrees=[]
    for args in arguments:
        require(type(args['log_rows'])is int and 1<=args['log_rows']<=13,'joint rows')
        h=derive_handoff(**args);d=(1<<args['log_rows'])*args['packing']
        require(128<=d<=262144 and 1<=len(h['lane_claims'])<=64,'joint shape')
        hs.append(h);degrees.append(d)
    D=max(degrees);n=D.bit_length()-1
    serial=[{k:(v.hex() if isinstance(v,bytes) else v) for k,v in a.items()} for a in arguments]
    digest=hash_parts(b'joint-opening-statement-v1',json.dumps(serial,sort_keys=True,separators=(',',':')).encode())
    t=Transcript(PROFILE.encode()+digest)
    draws,_=t.draw(b'joint-lane-and-branch-batching',2,4);eta,lam=map(tuple,draws)
    lambdas=power_values(lam,len(hs));powers=[];points=[];claim=ZERO
    for h,d,l in zip(hs,degrees,lambdas):
        ps=power_values(eta,len(h['lane_claims']));powers.append(ps)
        point=[ONE]*(n-(d.bit_length()-1))+[tuple(v) for v in h['packed_point']];points.append(point)
        branch=ZERO
        for p,v in zip(ps,h['lane_claims']):branch=add(branch,mul(p,tuple(v)))
        claim=add(claim,mul(l,branch))
    return hs,degrees,D,t,powers,lambdas,points,claim

def monomial_weight_at(point,u):
    result=ONE
    for z,x in zip(point,u):result=mul(result,add(ONE,mul(x,sub(z,ONE))))
    return result

def eq_weights(point):
    result=[ONE]
    for r in point:
        result=[mul(v,sub(ONE,r)) for v in result]+[mul(v,r) for v in result]
    return result

def equality_weight_at(u,at):
    result=ONE
    for r,x in zip(u,at):result=mul(result,add(mul(sub(ONE,r),sub(ONE,x)),mul(r,x)))
    return result

def context(stage,degree):
    if degree==1:return terminal_context(stage,1,4,1)[0]
    return b'NEAR-PQ384-JOINT-FOLD-ORACLE-V1/'+u64(degree)+stage

def branch_words(cache,powers,D):
    require(D%cache.degree==0,'degree lift');lift=D//cache.degree;out=array('I',[0])*(4*D)
    for lane,p in enumerate(powers):
        for k,c in enumerate(cache.coefficients(lane)):
            for j in range(4):out[4*k*lift+j]=(out[4*k*lift+j]+c*p[j])%P
    return out

def prove(caches,native,arguments):
    hs,degrees,D,t,powers,lambdas,points,claim=public(arguments);n=D.bit_length()-1
    require(len(caches)==len(arguments),'cache count')
    cs=[];ws=[]
    for cache,h,d,ps,z in zip(caches,hs,degrees,powers,points):
        require(cache.root.hex()==h['expected_root_hex'] and cache.context.hex()==h['context_hex'] and cache.degree==d and cache.lanes==len(ps),'cache binding')
        cs.append(branch_words(cache,ps,D))
        # Low lift coordinates have monomial weight1: repeat each original slot.
        w=array('I')
        for value in weights(h['packed_point']):w.extend(array('I',value)*(D//d))
        ws.append(w)
    reduction=[];u=[]
    for _ in range(n):
        q=[ZERO,ZERO,ZERO]
        for c,w,l in zip(cs,ws,lambdas):
            q=[add(a,mul(l,b)) for a,b in zip(q,native.quadratic_words(c,w))]
        wire=[list(v) for v in q];r,_,claim=round_start(t,wire,claim);reduction.append(wire);u.append(r)
        cs=[native.fold_words(c,r) for c in cs];ws=[native.fold_words(w,r) for w in ws]
    betas=[mul(l,monomial_weight_at(z,u)) for l,z in zip(lambdas,points)]
    expected=ZERO
    for c,b in zip(cs,betas):expected=add(expected,mul(b,tuple(c)))
    require(expected==claim,'joint reduction terminal')
    del cs,ws
    combined=array('I',[0])*(4*D)
    for cache,ps,beta in zip(caches,powers,betas):
        # Fuse lane and common-point weights; avoid a full Ext4 multiplication per slot.
        values=branch_words(cache,[mul(beta,p) for p in ps],D)
        for i,v in enumerate(values):combined[i]=(combined[i]+v)%P
    ws=flat(eq_weights(u));rounds=[];trees=[];degree=D
    while degree>1:
        wire=[list(v) for v in native.quadratic_words(combined,ws)]
        r,stage,claim=round_start(t,wire,claim)
        combined=native.fold_words(combined,r);ws=native.fold_words(ws,r);degree//=2
        tree=FlatTree(native.lde4_words(combined),context(stage,degree));trees.append(tree)
        t.commit(b'joint-next-oracle-root',tree.root);rounds.append({'quadratic':wire,'next_root':tree.root.hex()})
    terminal={'profile':'near-pq384-terminal-v1','coefficients':[[list(combined)]]}
    disclose(t,terminal,1)
    verify_terminal(terminal,expected_root=trees[-1].root,stage_binding=stage,degree_bound=1,domain_size=4,lanes=1,weights=[[list(ws)]],claim=claim)
    queries=[]
    for s in sample(t,4*D):
        queries.append({'sources':[c.opening(s%(2*d)) for c,d in zip(caches,degrees)],
                        'folds':[tree.opening(s%tree.half) for tree in trees]})
    return dict(profile=PROFILE,reduction=reduction,rounds=rounds,terminal=terminal,queries=queries)

def replay(proof,arguments):
    hs,degrees,D,t,powers,lambdas,points,claim=public(arguments);n=D.bit_length()-1
    require(type(proof)is dict and set(proof)=={'profile','reduction','rounds','terminal','queries'} and proof['profile']==PROFILE,'joint proof fields')
    require(isinstance(proof['reduction'],list) and len(proof['reduction'])==n,'joint reduction length');u=[]
    for wire in proof['reduction']:
        r,_,claim=round_start(t,wire,claim);u.append(r)
    betas=[mul(l,monomial_weight_at(z,u)) for l,z in zip(lambdas,points)]
    require(isinstance(proof['rounds'],list) and len(proof['rounds'])==n,'joint fold length')
    roots=[];contexts=[];challenges=[];degree=D
    for rd in proof['rounds']:
        require(type(rd)is dict and set(rd)=={'quadratic','next_root'},'joint round fields')
        r,stage,claim=round_start(t,rd['quadratic'],claim);challenges.append(r);degree//=2
        root=decode_hash(rd['next_root']);roots.append(root);contexts.append(context(stage,degree));t.commit(b'joint-next-oracle-root',root)
    disclose(t,proof['terminal'],1)
    verify_terminal(proof['terminal'],expected_root=roots[-1],stage_binding=stage,degree_bound=1,domain_size=4,lanes=1,
                    weights=[[[*equality_weight_at(u,challenges)]]],claim=claim)
    return hs,degrees,D,powers,betas,roots,contexts,challenges,sample(t,4*D)

def verify(proof,arguments):
    hs,degrees,D,powers,betas,roots,contexts,challenges,samples=replay(proof,arguments)
    require(isinstance(proof['queries'],list) and len(proof['queries'])==8,'joint query count')
    for s,q in zip(samples,proof['queries']):
        require(type(q)is dict and set(q)=={'sources','folds'},'joint query fields')
        require(isinstance(q['sources'],list) and len(q['sources'])==len(hs),'joint source count')
        require(isinstance(q['folds'],list) and len(q['folds'])==len(challenges),'joint fold count')
        a,b=ZERO,ZERO
        for opening,h,d,ps,beta in zip(q['sources'],hs,degrees,powers,betas):
            pair=check_opening(opening,bytes.fromhex(h['expected_root_hex']),bytes.fromhex(h['context_hex']),2*d,s%(2*d),True,ps)
            if d<D:
                value=pair[(s%(4*d))//(2*d)];pair=(value,value)
            a=add(a,mul(beta,pair[0]));b=add(b,mul(beta,pair[1]))
        degree=D
        for j,(opening,r) in enumerate(zip(q['folds'],challenges)):
            pair=check_opening(opening,roots[j],contexts[j],degree,s%degree,False,[ONE])
            omega=pow(440564289,(1<<27)//(4*degree),P);x=pow(omega,s%(2*degree),P)
            even=tuple(v*pow(2,-1,P)%P for v in add(a,b));odd=tuple(v*pow(2*x,-1,P)%P for v in sub(a,b))
            require(add(even,mul(r,sub(odd,even)))==pair[(s%(2*degree))//degree],'joint fold consistency')
            a,b=pair;degree//=2
    return True
