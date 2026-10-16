"""Experimental original packed roots -> scalar code-switch tail adapter.
Retains the weighted input reduction and authenticates original pair leaves.
No independent scalar source root is trusted. Not a certified PCS profile.
"""
import pq384_ext8_reference as f
import pq384_ext8_weighted as pcs
import ext8_code_switch_stage as stage
import ext8_code_switch_functional as algebra
from pq384_primitives import require,hash_parts
PROFILE='near-ext8-weighted-code-switch-diagnostic-v1'


def start(statement,parent,branches,claim,config):
    require(type(config)is dict and set(config)=={'queries','child_blowup','child_fold_bits','tail_steps'},'adapter config fields')
    require(type(config['queries'])is int and 1<=config['queries']<=4095,'adapter queries')
    require(type(config['tail_steps'])is list and len(config['tail_steps'])<=11,'tail schedule')
    bound_parent=hash_parts(PROFILE.encode(),parent,stage.canonical_json(config))
    degrees,D,contexts,t,claim=pcs.public(statement,bound_parent,branches,claim,config['queries'])
    stage.geometry(D//2,config['child_blowup'],config['child_fold_bits'])
    namespace=hash_parts(b'weighted-code-switch/namespace',t.seed).hex()
    return degrees,D,contexts,t,claim,namespace


def source_pair(ops,index,branches,degrees,D,contexts,betas):
    require(type(ops)is list and len(ops)==len(branches),'source branch count');a=b=f.ZERO
    for op,branch,d,ctx,powers in zip(ops,branches,degrees,contexts,betas):
        pair=pcs.read_opening(op,pcs.hashread(branch['root']),ctx,2*d,index%(2*d),True,powers)
        if d<D:pair=(pair[(index%(4*d))//(2*d)],)*2
        a=f.add(a,pair[0]);b=f.add(b,pair[1])
    return a,b


def reduce_prove(caches,native,branches,degrees,D,contexts,t,claim):
    require(len(caches)==len(branches),'cache count');states=[]
    for cache,b,d,ctx in zip(caches,branches,degrees,contexts):
        require(cache.root.hex()==b['root'] and cache.context==ctx and cache.degree==d and cache.lanes==pcs.lane_count(b),'source binding')
        low=(D//d).bit_length()-1
        for j in range(pcs.lane_count(b)):
            cs=[f.base(x) for x in cache.coefficients(j)];ws=pcs.families.lane_weights(b,j,native)
            q=native.quadratic(cs,ws);dot=f.add(q[0],f.evaluate(q,f.ONE));states.append([cs,ws,low,f.ONE,dot])
    reduction=[];u=[]
    for bit in range(D.bit_length()-1):
        q=[f.ZERO]*3
        for cs,ws,low,scale,dot in states:
            part=[dot,f.sub(f.ZERO,dot),f.ZERO] if bit<low else native.quadratic(cs,ws)
            q=[f.add(a,f.mul(scale,b)) for a,b in zip(q,part)]
        r,_,claim=pcs.round_start(t,q,claim);u.append(r);reduction.append([list(x) for x in q])
        for state in states:
            if bit<state[2]:state[3]=f.mul(state[3],f.sub(f.ONE,r))
            else:state[0]=native.affine_fold(state[0],r);state[1]=native.affine_fold(state[1],r)
    betas=pcs.betas(branches,degrees,D,u);combined=[f.ZERO]*D
    for cache,powers in zip(caches,betas):
        for j,power in enumerate(powers):
            for i,c in enumerate(cache.coefficients(j)):combined[i*(D//cache.degree)]=f.add(combined[i*(D//cache.degree)],f.scale(power,c))
    weights=pcs.eqs(u);require(algebra.dot(combined,weights)==claim,'reduced functional')
    return reduction,combined,weights,claim,betas


def initial_obligation(proof,config,branches,degrees,D,contexts,t,weights,claim,betas,namespace,r, *, native=None):
    z=stage.after_root(t,proof['child_root']);answer=f.canonical(proof['ood_answer'])
    indices=stage.after_answer(t,answer,2*D,config['queries'])
    ops=proof['source_openings'];require(type(ops)is list and len(ops)==len(indices),'adapter source query count')
    omega=pow(440564289,(1<<27)//(4*D),f.P);points=[z];answers=[answer]
    for index,opening in zip(indices,ops):
        pair=source_pair(opening,index,branches,degrees,D,contexts,betas)
        x=pow(omega,index,f.P);points.append(f.base(x*x%f.P))
        answers.append(algebra.fold_coset(pair,x,f.P-1,[r]))
    t.commit(b'code-switch/source-responses',stage.canonical_json(ops))
    mixers=[stage.draw(t,b'code-switch/constraint-mixer') for _ in points]
    weights,claim=(algebra.inject if native is None else native.inject)(weights,claim,points,answers,mixers)
    return dict(degree=D//2,blowup=config['child_blowup'],fold_bits=config['child_fold_bits'],namespace=namespace,
                root=proof['child_root'],parent=t.seed.hex(),weights=[list(w) for w in weights],claim=list(claim))


def prove(caches,native,statement,parent,branches,claim,config):
    degrees,D,contexts,t,claim,namespace=start(statement,parent,branches,claim,config)
    reduction,cs,weights,claim,betas=reduce_prove(caches,native,branches,degrees,D,contexts,t,claim)
    q=[list(x) for x in native.quadratic(cs,weights)];r,claim=stage.round_step(t,q,claim)
    cs=native.affine_fold(cs,r);weights=native.affine_fold(weights,r)
    child=stage.tree(cs,namespace,config['child_blowup'],config['child_fold_bits'],native=native)
    # Generate responses from a transcript copy; verification reconstructs draws.
    replay=stage.h.Transcript(b'');replay.seed=t.seed
    z=stage.after_root(replay,child['root'].hex());answer=f.evaluate(cs,z)
    indices=stage.after_answer(replay,answer,2*D,config['queries'])
    first=dict(quadratic=q,child_root=child['root'].hex(),ood_answer=list(answer),
               source_openings=[[cache.opening(i%(2*cache.degree)) for cache in caches] for i in indices])
    state=initial_obligation(first,config,branches,degrees,D,contexts,t,weights,claim,betas,namespace,r,native=native)
    require(algebra.dot(cs,state['weights'])==f.canonical(state['claim']),'first continuing functional')
    tail=[]
    for step in config['tail_steps']:
        proof,state,cs=stage.prove_stage(cs,stage.follow_config(state,step),state['weights'],state['claim'],native=native);tail.append(proof)
    require(state['fold_bits']==0,'adapter terminal schedule');stage.close_terminal(state,cs)
    return dict(profile=PROFILE,reduction=reduction,first=first,tail=tail,terminal=[list(c) for c in cs])


def verify(proof,statement,parent,branches,claim,config, *, native=None):
    degrees,D,contexts,t,claim,namespace=start(statement,parent,branches,claim,config)
    require(type(proof)is dict and set(proof)=={'profile','reduction','first','tail','terminal'} and proof['profile']==PROFILE,'adapter proof fields')
    require(type(proof['reduction'])is list and len(proof['reduction'])==D.bit_length()-1,'input reduction length')
    u=[]
    for q in proof['reduction']:r,_,claim=pcs.round_start(t,q,claim);u.append(r)
    betas=pcs.betas(branches,degrees,D,u);weights=pcs.eqs(u)
    first=proof['first'];require(type(first)is dict and set(first)=={'quadratic','child_root','ood_answer','source_openings'},'first stage fields')
    r,claim=stage.round_step(t,first['quadratic'],claim);weights=(f.affine_fold if native is None else native.affine_fold)(weights,r)
    state=initial_obligation(first,config,branches,degrees,D,contexts,t,weights,claim,betas,namespace,r,native=native)
    require(type(proof['tail'])is list and len(proof['tail'])==len(config['tail_steps']),'tail length')
    for p,step in zip(proof['tail'],config['tail_steps']):state=stage.verify_stage(p,stage.follow_config(state,step),state['weights'],state['claim'],native=native)
    require(state['fold_bits']==0,'adapter terminal schedule')
    return stage.close_terminal(state,proof['terminal'])


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    p=argparse.ArgumentParser();p.add_argument('--proof',type=Path,required=True);p.add_argument('--statement',type=Path,required=True);p.add_argument('--native-library',type=Path);a=p.parse_args()
    proof=json.loads(a.proof.read_text());s=json.loads(a.statement.read_text())
    from pq384_ext8_native import Kernel
    native=Kernel(a.native_library) if a.native_library else None
    verify(proof,bytes.fromhex(s['statement']),bytes.fromhex(s['parent']),s['branches'],s['claim'],s['config'],native=native)
    print('PASS experimental packed-root code-switch adapter; no proximity/QROM certificate.')
