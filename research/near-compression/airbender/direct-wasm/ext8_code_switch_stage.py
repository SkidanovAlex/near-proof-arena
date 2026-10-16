"""Experimental scalar Ext8 code-switch stage, NOT a certified PCS.
verify_stage returns an unproved continuing obligation. Only close_terminal
checks it against a disclosed, exactly sized coefficient vector and root.
No source extraction, proximity, whole-protocol or QROM claim is made.
"""
import json
import pq384_ext8_reference as f
import pq384_primitives as h
import ext8_code_switch_functional as algebra
from pq384_ext8_reusable import extbytes,hashread,sample
PROFILE='near-ext8-code-switch-stage-diagnostic-v1'


def canonical_json(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()
def vector(values):return b''.join(extbytes(v) for v in values)
def draw(t,label):return tuple(t.draw(label,1,8)[0][0])


def geometry(degree,blowup,fold_bits):
    h.require(type(degree)is int and 2<=degree<=262144 and degree&(degree-1)==0,'degree')
    h.require(type(blowup)is int and 2<=blowup<=256 and blowup&(blowup-1)==0,'blowup')
    h.require(type(fold_bits)is int and 0<=fold_bits<=min(4,degree.bit_length()-1),'fold bits')
    N=degree*blowup;h.require(N<=1<<22,'reference/native domain cap')
    return N,N//(1<<fold_bits),pow(31,(f.P-1)//N,f.P)


def context(namespace,degree,blowup,fold_bits):
    geometry(degree,blowup,fold_bits);hashread(namespace)
    return h.hash_parts(b'ext8/code-switch/coset-context-v1',bytes.fromhex(namespace),
        h.u64(degree),h.u64(blowup),h.u64(fold_bits),b'Ext8-natural-coset-8xu32')


def tree(coefficients,namespace,blowup,fold_bits, *, native=None):
    cs=[f.canonical(x) for x in coefficients];d=len(cs);N,count,omega=geometry(d,blowup,fold_bits)
    ctx=context(namespace,d,blowup,fold_bits);padded=cs+[f.ZERO]*(N-d);values=f.fft(padded,omega) if native is None else native.fft(padded)
    leaves=[vector([values[i+j*count] for j in range(1<<fold_bits)]) for i in range(count)]
    root,layers=h.merkle_tree(leaves,ctx)
    return dict(root=root,context=ctx,layers=layers,values=values,count=count,degree=d,blowup=blowup,fold_bits=fold_bits)


def opening(cache,index):
    return dict(values=[list(cache['values'][index+j*cache['count']]) for j in range(1<<cache['fold_bits'])],
                path=[x.hex() for x in h.merkle_path(cache['layers'],index)])


def start(config,weights,claim):
    h.require(type(config)is dict and set(config)=={'profile','degree','blowup','fold_bits','next_blowup','next_fold_bits','queries','namespace','parent','root'},'stage config fields')
    h.require(config['profile']==PROFILE,'stage profile')
    N,count,omega=geometry(config['degree'],config['blowup'],config['fold_bits'])
    h.require(config['fold_bits']>0,'positive stage folding')
    child_degree=config['degree']>>config['fold_bits']
    geometry(child_degree,config['next_blowup'],config['next_fold_bits'])
    h.require(type(config['queries'])is int and 1<=config['queries']<=4095,'query count')
    for key in ('namespace','parent','root'):hashread(config[key])
    h.require(len(weights)==config['degree'],'weight shape');weights=[f.canonical(w) for w in weights];claim=f.canonical(claim)
    seed=h.hash_parts(PROFILE.encode(),canonical_json(config),vector(weights),extbytes(claim))
    return h.Transcript(seed),weights,claim,N,count,omega


def round_step(t,wire,claim):
    h.require(type(wire)is list and len(wire)==3,'quadratic shape');q=[f.canonical(x) for x in wire]
    h.require(f.add(q[0],f.evaluate(q,f.ONE))==claim,'sumcheck endpoint')
    t.commit(b'code-switch/quadratic',vector(q));r=draw(t,b'code-switch/fold-challenge')
    return r,f.evaluate(q,r)


def after_root(t,root):
    t.commit(b'code-switch/child-root',hashread(root))
    return draw(t,b'code-switch/ood-point')


def after_answer(t,answer,count,queries):
    t.commit(b'code-switch/ood-answer',extbytes(answer))
    return sample(t,count,queries)


def obligation(config,t,weights,claim,child_root,z,answer,indices,openings,challenges,N,count,omega, *, native=None):
    h.require(type(openings)is list and len(openings)==len(indices),'source query count')
    points=[z];answers=[f.canonical(answer)];ctx=context(config['namespace'],config['degree'],config['blowup'],config['fold_bits'])
    for index,op in zip(indices,openings):
        h.require(type(op)is dict and set(op)=={'values','path'},'source opening fields')
        h.require(type(op['values'])is list and len(op['values'])==1<<config['fold_bits'],'source coset shape')
        values=[f.canonical(x) for x in op['values']]
        h.require(type(op['path'])is list,'source path shape')
        h.verify_path(hashread(config['root']),ctx,count,index,vector(values),[hashread(x) for x in op['path']])
        x=pow(omega,index,f.P);root=pow(omega,count,f.P)
        answers.append(algebra.fold_coset(values,x,root,challenges))
        points.append(f.base(pow(x,1<<config['fold_bits'],f.P)))
    # Bind every authenticated response before drawing any constraint mixer.
    t.commit(b'code-switch/source-responses',canonical_json(openings))
    mixers=[draw(t,b'code-switch/constraint-mixer') for _ in points]
    weights,claim=(algebra.inject if native is None else native.inject)(weights,claim,points,answers,mixers)
    return dict(degree=config['degree']>>config['fold_bits'],blowup=config['next_blowup'],fold_bits=config['next_fold_bits'],
                namespace=config['namespace'],root=child_root,parent=t.seed.hex(),weights=[list(w) for w in weights],claim=list(claim))


def prove_stage(coefficients,config,weights,claim, *, native=None):
    t,weights,claim,N,count,omega=start(config,weights,claim)
    cs=[f.canonical(c) for c in coefficients];h.require(len(cs)==config['degree'],'source coefficient shape')
    cache=tree(cs,config['namespace'],config['blowup'],config['fold_bits'],native=native)
    h.require(cache['root'].hex()==config['root'],'source root binding')
    rounds=[];challenges=[]
    for _ in range(config['fold_bits']):
        q=[list(x) for x in (f.quadratic if native is None else native.quadratic)(cs,weights)];r,claim=round_step(t,q,claim);rounds.append(q);challenges.append(r)
        cs=(f.affine_fold if native is None else native.affine_fold)(cs,r);weights=(f.affine_fold if native is None else native.affine_fold)(weights,r)
    child=tree(cs,config['namespace'],config['next_blowup'],config['next_fold_bits'],native=native);child_root=child['root'].hex()
    z=after_root(t,child_root);answer=f.evaluate(cs,z)
    indices=after_answer(t,answer,count,config['queries']);ops=[opening(cache,i) for i in indices]
    state=obligation(config,t,weights,claim,child_root,z,answer,indices,ops,challenges,N,count,omega,native=native)
    h.require(algebra.dot(cs,state['weights'])==f.canonical(state['claim']),'honest continuing functional')
    return dict(rounds=rounds,child_root=child_root,ood_answer=list(answer),source_openings=ops),state,cs


def verify_stage(proof,config,weights,claim, *, native=None):
    t,weights,claim,N,count,omega=start(config,weights,claim)
    h.require(type(proof)is dict and set(proof)=={'rounds','child_root','ood_answer','source_openings'},'stage proof fields')
    h.require(type(proof['rounds'])is list and len(proof['rounds'])==config['fold_bits'],'round count')
    challenges=[]
    for q in proof['rounds']:
        r,claim=round_step(t,q,claim);challenges.append(r);weights=(f.affine_fold if native is None else native.affine_fold)(weights,r)
    z=after_root(t,proof['child_root']);answer=f.canonical(proof['ood_answer'])
    indices=after_answer(t,answer,count,config['queries'])
    return obligation(config,t,weights,claim,proof['child_root'],z,answer,indices,proof['source_openings'],challenges,N,count,omega,native=native)


def close_terminal(state,coefficients):
    h.require(type(state)is dict and set(state)=={'degree','blowup','fold_bits','namespace','root','parent','weights','claim'},'terminal state fields')
    hashread(state['parent']);h.require(len(coefficients)==state['degree']==len(state['weights']),'terminal shape')
    cs=[f.canonical(c) for c in coefficients]
    cache=tree(cs,state['namespace'],state['blowup'],state['fold_bits'])
    h.require(cache['root'].hex()==state['root'],'terminal root binding')
    h.require(algebra.dot(cs,state['weights'])==f.canonical(state['claim']),'terminal residual')
    return True


def follow_config(state,step):
    h.require(type(step)is dict and set(step)=={'next_blowup','next_fold_bits','queries'},'schedule step fields')
    return {k:state[k] for k in ('degree','blowup','fold_bits','namespace','root','parent')}|dict(profile=PROFILE,**step)


def chain_start(initial,schedule):
    h.require(type(schedule)is list and len(schedule)<=11,'schedule length')
    config=dict(initial)
    config['parent']=h.hash_parts(b'code-switch/chain-schedule',hashread(initial['parent']),canonical_json(schedule)).hex()
    return config


def prove_chain(coefficients,initial,weights,claim,schedule, *, native=None):
    config=chain_start(initial,schedule);stages=[];cs=coefficients
    for i in range(1+len(schedule)):
        proof,state,cs=prove_stage(cs,config,weights,claim,native=native);stages.append(proof)
        if i<len(schedule):config=follow_config(state,schedule[i]);weights=state['weights'];claim=state['claim']
    h.require(state['fold_bits']==0,'terminal schedule')
    close_terminal(state,cs)
    return dict(stages=stages,terminal=[list(c) for c in cs])


def verify_chain(proof,initial,weights,claim,schedule, *, native=None):
    h.require(type(proof)is dict and set(proof)=={'stages','terminal'},'chain proof fields')
    h.require(type(proof['stages'])is list and len(proof['stages'])==1+len(schedule),'stage count')
    config=chain_start(initial,schedule)
    for i,p in enumerate(proof['stages']):
        state=verify_stage(p,config,weights,claim,native=native)
        if i<len(schedule):config=follow_config(state,schedule[i]);weights=state['weights'];claim=state['claim']
    h.require(state['fold_bits']==0,'terminal schedule')
    return close_terminal(state,proof['terminal'])


if __name__=='__main__':
    import argparse
    from pathlib import Path
    p=argparse.ArgumentParser();p.add_argument('--proof',type=Path,required=True);p.add_argument('--statement',type=Path,required=True);p.add_argument('--native-library',type=Path);a=p.parse_args()
    proof=json.loads(a.proof.read_text());statement=json.loads(a.statement.read_text())
    from pq384_ext8_native import Kernel
    native=Kernel(a.native_library) if a.native_library else None
    verify_chain(proof,statement['config'],statement['weights'],statement['claim'],statement['schedule'],native=native)
    print('PASS experimental code-switch chain; no extraction/proximity/QROM certificate.')
