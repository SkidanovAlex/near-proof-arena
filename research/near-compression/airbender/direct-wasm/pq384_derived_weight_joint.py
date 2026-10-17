"""Recursion-oriented weighted PCS, valid ONLY for verifier-derived weights.

Standalone callers cannot use arbitrary adaptive lane weights under this API.
The integrated seed-GKR bus verifier derives them deterministically from its
bound public statement and final GKR transcript; the proof contains none.
This dependency replaces redundant JSON hashing, not any algebraic check.
"""
"""General lane-functional joint PCS diagnostic; Q8/Ext4, no security claim.

Externally derived weights bind the one aggregate claim. No proof-selected
column claims or points, and no division by exceptional challenge factors.
Adaptive virtual-oracle batching and proximity/RBR/QROM remain unproved.
"""
from array import array
import json
import pq384_joint_opening as old
from pq384_terminal_input_weights import lane_weights,lane_weight_mle
from pq384_primitives import Transcript,require,hash_parts,u64,P
from packed_claim_handoff import packing_context,canonical_ext as ext,vector_bytes
from pq384_one_fold import ZERO,ONE,decode_hash
from pq384_terminal import verify_terminal
from pq384_cached_prover import FlatTree,flat
from pq384_global_chain import round_start,disclose,sample
from pq384_batched_fold import check_opening
from check_whir_handoff import add,sub,mul
PROFILE='near-pq384-derived-weight-joint-v1'


def public(statement,parent,branches,claim):
    require(type(statement)is bytes and type(parent)is bytes,'statement binding')
    require(isinstance(branches,list) and 1<=len(branches)<=128,'branch count')
    degrees=[];contexts=[]
    for b in branches:
        require(set(b)=={'root','log_rows','width','packing','row_point','lanes'},'branch fields')
        n=b['log_rows'];p=b['packing'];w=b['width'];require(type(n)is int and 1<=n<=13,'row dimension')
        contexts.append(packing_context(n,w,p));d=(1<<n)*p;require(128<=d<=262144,'degree');degrees.append(d)
        decode_hash(b['root']);require(len(b['row_point'])==n,'row point');[ext(x) for x in b['row_point']]
        require(len(b['lanes'])==(w+p-1)//p<=64,'lane count')
        for j,lane in enumerate(b['lanes']):
            require(len(lane)==2 and all(len(x)==p for x in lane),'lane weight shape')
            for side in lane:
                for c,x in enumerate(side):
                    value=ext(x)
                    if j*p+c>=w:require(value==ZERO,'padding weight must be zero')
    # Integrated caller derives every lane weight from verified GKR queries,
    # canonical input slots, and row points; it accepts no proof-selected weights.
    metadata=b''.join(bytes.fromhex(b['root'])+u64(b['log_rows'])+u64(b['width'])+u64(b['packing'])+vector_bytes([ext(x) for x in b['row_point']]) for b in branches)
    digest=hash_parts(b'derived-weight-joint-public-v1',statement,parent,metadata,vector_bytes([ext(claim)]))
    return degrees,max(degrees),contexts,Transcript(PROFILE.encode()+digest),ext(claim)


def context(stage,degree):
    return old.context(hash_parts(b'weighted-joint-stage-v1',stage),degree)


def betas(branches,degrees,D,u):
    return [[lane_weight_mle([ext(x) for x in b['row_point']],[ext(x) for x in a],[ext(x) for x in c],u[(D//d).bit_length()-1:]) for a,c in b['lanes']] for b,d in zip(branches,degrees)]


def prove(caches,native,statement,parent,branches,claim):
    degrees,D,contexts,t,claim=public(statement,parent,branches,claim);n=D.bit_length()-1
    require(len(caches)==len(branches),'cache count');states=[]
    for cache,b,d,ctx in zip(caches,branches,degrees,contexts):
        require(cache.root.hex()==b['root'] and cache.context==ctx and cache.degree==d,'cache binding')
        low=(D//d).bit_length()-1
        for j,(ac,bc) in enumerate(b['lanes']):
            c=array('I')
            for x in cache.coefficients(j):c.extend((x,0,0,0))
            w=flat(lane_weights([ext(x) for x in b['row_point']],[ext(x) for x in ac],[ext(x) for x in bc]))
            q=native.quadratic_words(c,w);dot=add(add(q[0],q[0]),add(q[1],q[2]))
            states.append([c,w,low,ONE,dot])
    reduction=[];u=[]
    for round_index in range(n):
        q=[ZERO,ZERO,ZERO]
        for c,w,low,scale,dot in states:
            qq=[dot,sub(ZERO,dot),ZERO] if round_index<low else native.quadratic_words(c,w)
            q=[add(a,mul(scale,b)) for a,b in zip(q,qq)]
        wire=[list(x) for x in q];r,_,claim=round_start(t,wire,claim);u.append(r);reduction.append(wire)
        for s in states:
            if round_index<s[2]:s[3]=mul(s[3],sub(ONE,r))
            else:s[0]=native.fold_words(s[0],r);s[1]=native.fold_words(s[1],r)
    bs=betas(branches,degrees,D,u);at=ZERO
    for state,beta in zip(states,[x for row in bs for x in row]):at=add(at,mul(mul(tuple(state[0]),state[3]),beta))
    require(at==claim,'weighted reduction terminal');del states
    combined=array('I',[0])*(4*D)
    for cache,bb in zip(caches,bs):
        v=old.branch_words(cache,bb,D)
        for i,x in enumerate(v):combined[i]=(combined[i]+x)%P
    w=flat(old.eq_weights(u));rounds=[];trees=[];degree=D
    while degree>1:
        wire=[list(x) for x in native.quadratic_words(combined,w)];r,stage,claim=round_start(t,wire,claim)
        combined=native.fold_words(combined,r);w=native.fold_words(w,r);degree//=2
        tree=FlatTree(native.lde4_words(combined),context(stage,degree));trees.append(tree)
        t.commit(b'weighted-joint-next-root',tree.root);rounds.append(dict(quadratic=wire,next_root=tree.root.hex()))
    terminal=dict(profile='near-pq384-terminal-v1',coefficients=[[list(combined)]])
    disclose(t,terminal,1)
    verify_terminal(terminal,expected_root=trees[-1].root,stage_binding=hash_parts(b'weighted-joint-stage-v1',stage),degree_bound=1,domain_size=4,lanes=1,weights=[[list(w)]],claim=claim)
    queries=[dict(sources=[c.opening(s%(2*d)) for c,d in zip(caches,degrees)],folds=[tree.opening(s%tree.half) for tree in trees]) for s in sample(t,4*D)]
    return dict(profile=PROFILE,reduction=reduction,rounds=rounds,terminal=terminal,queries=queries)


def replay(proof,statement,parent,branches,claim):
    degrees,D,contexts,t,claim=public(statement,parent,branches,claim);n=D.bit_length()-1
    require(set(proof)=={'profile','reduction','rounds','terminal','queries'} and proof['profile']==PROFILE,'proof fields')
    require(len(proof['reduction'])==len(proof['rounds'])==n,'round lengths');u=[]
    for wire in proof['reduction']:
        r,_,claim=round_start(t,wire,claim);u.append(r)
    bs=betas(branches,degrees,D,u);roots=[];fold_contexts=[];challenges=[];degree=D
    for rd in proof['rounds']:
        require(set(rd)=={'quadratic','next_root'},'round fields');r,stage,claim=round_start(t,rd['quadratic'],claim);challenges.append(r);degree//=2
        root=decode_hash(rd['next_root']);roots.append(root);fold_contexts.append(context(stage,degree));t.commit(b'weighted-joint-next-root',root)
    disclose(t,proof['terminal'],1)
    verify_terminal(proof['terminal'],expected_root=roots[-1],stage_binding=hash_parts(b'weighted-joint-stage-v1',stage),degree_bound=1,domain_size=4,lanes=1,weights=[[[*old.equality_weight_at(u,challenges)]]],claim=claim)
    return degrees,D,contexts,bs,roots,fold_contexts,challenges,sample(t,4*D)


def verify(proof,statement,parent,branches,claim):
    degrees,D,contexts,bs,roots,fold_contexts,challenges,samples=replay(proof,statement,parent,branches,claim)
    require(len(proof['queries'])==8,'query count')
    for s,q in zip(samples,proof['queries']):
        require(set(q)=={'sources','folds'} and len(q['sources'])==len(branches) and len(q['folds'])==len(challenges),'query shape');a,b=ZERO,ZERO
        for op,branch,d,ctx,beta in zip(q['sources'],branches,degrees,contexts,bs):
            pair=check_opening(op,decode_hash(branch['root']),ctx,2*d,s%(2*d),True,beta)
            if d<D:pair=(pair[(s%(4*d))//(2*d)],)*2
            a=add(a,pair[0]);b=add(b,pair[1])
        degree=D
        for j,(op,r) in enumerate(zip(q['folds'],challenges)):
            pair=check_opening(op,roots[j],fold_contexts[j],degree,s%degree,False,[ONE])
            omega=pow(440564289,(1<<27)//(4*degree),P);x=pow(omega,s%(2*degree),P)
            even=tuple(v*pow(2,-1,P)%P for v in add(a,b));odd=tuple(v*pow(2*x,-1,P)%P for v in sub(a,b))
            require(add(even,mul(r,sub(odd,even)))==pair[(s%(2*degree))//degree],'weighted fold consistency');a,b=pair;degree//=2
    return True
