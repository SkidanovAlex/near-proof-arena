"""Separately versioned affine-fold/global-query experiment, NOT a security theorem.

All quadratics/roots and disclosed terminal precede shared projection queries.
Terminal1 is the default baseline; terminal64 has an additional truncation proof
obligation. Virtual source batching, proximity, RBR and QROM remain unproved.
"""
from array import array
from pq384_primitives import Transcript,require,P,u64
from packed_claim_handoff import derive_handoff,vector_bytes,canonical_ext
from pq384_one_fold import ZERO,ONE,weights,polynomial,decode_hash
from pq384_terminal import terminal_context,verify_terminal
from pq384_cached_prover import FlatTree,flat,tuples
from pq384_batched_fold import check_opening
from check_whir_handoff import add,sub,mul

PROFILE='near-pq384-global-chain-v1'
QUERIES=8

def public(args,terminal_degree):
    require(type(terminal_degree)is int and terminal_degree in (1,64),'terminal profile')
    require(type(args['log_rows'])is int and 1<=args['log_rows']<=13,'row profile')
    h=derive_handoff(**args);degree=(1<<args['log_rows'])*args['packing']
    require(128<=degree<=262144 and 1<=len(h['lane_claims'])<=64,'opening profile')
    t=Transcript(b'NEAR-PQ384-GLOBAL-CHAIN-DIAGNOSTIC-V1/Q8/'+u64(terminal_degree))
    t.commit(b'packed-handoff',bytes.fromhex(h['transcript_seed_hex']))
    draw,_=t.draw(b'lane-batching-challenge',1,4);alpha=tuple(draw[0]);powers=[];power=ONE;claim=ZERO
    for value in h['lane_claims']:
        powers.append(power);claim=add(claim,mul(power,tuple(value)));power=mul(power,alpha)
    return h,t,degree,powers,claim

def context(stage,degree,terminal_degree):
    if degree==terminal_degree:return terminal_context(stage,degree,4*degree,1)[0]
    return (b'NEAR-PQ384-GLOBAL-CHAIN-ORACLE-V1/Ext4-v4=11/natural-domain/lane-pairs/le-u32'
            +u64(len(stage))+stage+b''.join(u64(v) for v in (P,degree,4*degree,terminal_degree)))

def round_start(t,wire,claim):
    require(isinstance(wire,list) and len(wire)==3,'quadratic shape');cs=[canonical_ext(v) for v in wire]
    require(add(cs[0],add(add(cs[0],cs[1]),cs[2]))==claim,'quadratic endpoints')
    t.commit(b'sumcheck-quadratic',vector_bytes(cs));draw,_=t.draw(b'fold-challenge',1,4)
    r=tuple(draw[0]);return r,t.seed,polynomial(cs,r)

def disclose(t,terminal,degree):
    require(type(terminal)is dict and set(terminal)=={'profile','coefficients'} and
            terminal['profile']=='near-pq384-terminal-v1','terminal fields')
    rows=terminal['coefficients'];require(isinstance(rows,list) and len(rows)==1 and
            isinstance(rows[0],list) and len(rows[0])==degree,'terminal coefficients')
    t.commit(b'disclosed-terminal-before-queries',u64(degree)+vector_bytes([canonical_ext(v) for v in rows[0]]))

def sample(t,domain):
    out=[]
    for _ in range(4096):
        values,_=t.draw(b'global-chain-domain-index',1,1);v=values[0][0]
        if v<P//domain*domain:out.append(v%domain)
        if len(out)==QUERIES:return out
    raise ValueError('query sampler exhausted')

def prove_cached(cache,native,*,terminal_degree=1,**args):
    h,t,degree,powers,claim=public(args,terminal_degree);initial=degree
    require(cache.root==args['expected_root'] and cache.context.hex()==h['context_hex'] and
            cache.degree==degree and cache.lanes==len(powers),'source cache identity')
    cs=array('I',[0])*(4*degree)
    for lane,power in enumerate(powers):
        for i,c in enumerate(cache.coefficients(lane)):
            for k in range(4):cs[4*i+k]=(cs[4*i+k]+power[k]*c)%P
    ws=flat(weights(h['packed_point']));rounds=[];oracles=[cache]
    while degree>terminal_degree:
        wire=[list(v) for v in native.quadratic_words(cs,ws)]
        r,stage,claim=round_start(t,wire,claim)
        cs=native.fold_words(cs,r);ws=native.fold_words(ws,r);degree//=2
        nxt=FlatTree(native.lde4_words(cs),context(stage,degree,terminal_degree))
        t.commit(b'next-oracle-root',nxt.root);oracles.append(nxt)
        rounds.append({'quadratic':wire,'next_root':nxt.root.hex()})
    terminal={'profile':'near-pq384-terminal-v1','coefficients':[[list(v) for v in tuples(cs)]]}
    disclose(t,terminal,terminal_degree)
    verify_terminal(terminal,expected_root=oracles[-1].root,stage_binding=stage,degree_bound=degree,
                    domain_size=4*degree,lanes=1,weights=[[list(v) for v in tuples(ws)]],claim=claim)
    queries=[]
    for s in sample(t,4*initial):
        chain=[];degree=initial
        for j in range(len(rounds)):
            chain.append({'source':oracles[j].opening(s%(2*degree)),
                          'next':oracles[j+1].opening(s%degree)})
            degree//=2
        queries.append(chain)
    return {'profile':PROFILE,'rounds':rounds,'terminal':terminal,'queries':queries}

def verify(proof,*,terminal_degree=1,**args):
    h,t,degree,powers,claim=public(args,terminal_degree);initial=degree
    require(type(proof)is dict and set(proof)=={'profile','rounds','terminal','queries'} and proof['profile']==PROFILE,'proof fields')
    rounds=proof['rounds'];count=degree.bit_length()-terminal_degree.bit_length()
    require(isinstance(rounds,list) and len(rounds)==count,'round count')
    roots=[args['expected_root']];contexts=[bytes.fromhex(h['context_hex'])];challenges=[];factor=ONE
    for j,rd in enumerate(rounds):
        require(type(rd)is dict and set(rd)=={'quadratic','next_root'},'round fields')
        r,stage,claim=round_start(t,rd['quadratic'],claim);challenges.append(r)
        factor=mul(factor,add(ONE,mul(r,sub(tuple(h['packed_point'][j]),ONE))))
        degree//=2;root=decode_hash(rd['next_root']);roots.append(root);contexts.append(context(stage,degree,terminal_degree))
        t.commit(b'next-oracle-root',root)
    disclose(t,proof['terminal'],terminal_degree)
    ws=[mul(factor,w) for w in weights(h['packed_point'][count:])]
    verify_terminal(proof['terminal'],expected_root=roots[-1],stage_binding=stage,degree_bound=degree,
                    domain_size=4*degree,lanes=1,weights=[[list(v) for v in ws]],claim=claim)
    require(isinstance(proof['queries'],list) and len(proof['queries'])==QUERIES,'global query count')
    for s,chain in zip(sample(t,4*initial),proof['queries']):
        require(isinstance(chain,list) and len(chain)==count,'chain length');degree=initial
        for j,(q,r) in enumerate(zip(chain,challenges)):
            require(type(q)is dict and set(q)=={'source','next'},'chain query fields')
            i=s%(2*degree)
            a,b=check_opening(q['source'],roots[j],contexts[j],2*degree,i,j==0,powers)
            pair=check_opening(q['next'],roots[j+1],contexts[j+1],degree,s%degree,False,powers)
            omega=pow(440564289,(1<<27)//(4*degree),P);x=pow(omega,i,P)
            even=tuple(v*pow(2,-1,P)%P for v in add(a,b))
            odd=tuple(v*pow(2*x,-1,P)%P for v in sub(a,b))
            require(add(even,mul(r,sub(odd,even)))==pair[i//degree],'global chain fold consistency')
            degree//=2
    return True

if __name__=='__main__':
    import json,sys
    from pathlib import Path
    proof=json.loads(Path(sys.argv[1]).read_text());args=json.loads(Path(sys.argv[2]).read_text())
    for key in ('statement','parent_binding','expected_root'):args[key]=bytes.fromhex(args[key])
    assert verify(proof,terminal_degree=int(sys.argv[3]),**args)
    print('PASS: global-chain diagnostic; no inherited security theorem')
