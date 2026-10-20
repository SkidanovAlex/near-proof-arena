"""Hybrid arithmetic verifier for the unchanged closed-derived experimental wire.
Representation-only fork; never accepts an externally supplied functional state.
"""
import ext8_closed_derived_switch as closed
from ext8_structured_functional import Functional
import pq384_ext8_reference as f
from pq384_ext8_terminal_gkr import eqs
import ext8_code_switch_functional as algebra


class Weights:
    def __init__(self,state,native,events):self.state=state;self.native=native;self.events=events;self.choose()
    def __len__(self):return self.state.size if isinstance(self.state,Functional) else len(self.state)
    def choose(self):
        if isinstance(self.state,Functional) and len(self.state.point)+1+2*len(self.state.powers)>=self.state.size:
            n=self.state.size;terms=len(self.state.powers);self.state=self.expanded()
            self.events.append(dict(kind='materialize',degree=n,terms=terms))
    def expanded(self):
        if not isinstance(self.state,Functional):return self.state
        s=self.state;weights=[f.mul(s.tensor_scale,x) for x in eqs(s.point)]
        if s.powers:
            mixers,points=zip(*s.powers)
            weights,_=(self.native.inject if self.native else algebra.inject)(weights,f.ZERO,points,[f.ZERO]*len(points),mixers)
        return weights
    def fold(self,r):
        if isinstance(self.state,Functional):result=self.state.fold(r)
        else:result=(self.native.affine_fold if self.native else f.affine_fold)(self.state,r)
        self.events.append(dict(kind='fold',degree=len(self),structured=isinstance(self.state,Functional)))
        return Weights(result,self.native,self.events)
    def inject(self,claim,points,answers,mixers):
        if not len(points)==len(answers)==len(mixers):raise ValueError('injection shape')
        points,answers,mixers=([f.canonical(x) for x in seq] for seq in (points,answers,mixers));claim=f.canonical(claim)
        if isinstance(self.state,Functional):
            result=self.state.inject(points,mixers)
            for m,a in zip(mixers,answers):claim=f.add(claim,f.mul(m,a))
        else:result,claim=(self.native.inject if self.native else algebra.inject)(self.state,claim,points,answers,mixers)
        self.events.append(dict(kind='inject',degree=len(self),points=len(points),structured=isinstance(self.state,Functional)))
        return Weights(result,self.native,self.events),claim


class Backend:
    def affine_fold(self,weights,r):return weights.fold(r)
    def inject(self,weights,claim,points,answers,mixers):return weights.inject(claim,points,answers,mixers)


stage=closed._clone(closed._stage,__name__+'._stage')
h=stage.h
require=h.require
hashread=stage.hashread
vector=stage.vector
context=stage.context
draw=stage.draw
canonical_json=stage.canonical_json
source_pair=closed._adapter.source_pair


def start(config,weights,claim):
    h.require(type(config)is dict and set(config)=={'profile','degree','blowup','fold_bits','next_blowup','next_fold_bits','queries','namespace','parent','root'},'stage config fields')
    h.require(config['profile']==closed.STAGE_PROFILE,'closed stage profile')
    N,count,omega=stage.geometry(config['degree'],config['blowup'],config['fold_bits'])
    h.require(config['fold_bits']>0,'positive stage folding')
    stage.geometry(config['degree']>>config['fold_bits'],config['next_blowup'],config['next_fold_bits'])
    h.require(type(config['queries'])is int and 1<=config['queries']<=4095,'query count')
    for key in ('namespace','parent','root'):hashread(config[key])
    h.require(isinstance(weights,Weights) and len(weights)==config['degree'],'derived hybrid weight shape');claim=f.canonical(claim)
    seed=h.hash_parts(closed.STAGE_PROFILE.encode(),closed.DERIVATION,canonical_json(config),stage.extbytes(claim))
    return h.Transcript(seed),weights,claim,N,count,omega


def close_terminal(state,coefficients):
    h.require(type(state)is dict and set(state)=={'degree','blowup','fold_bits','namespace','root','parent','weights','claim'},'terminal state fields')
    hashread(state['parent']);h.require(len(coefficients)==state['degree']==len(state['weights']),'terminal shape')
    cs=[f.canonical(c) for c in coefficients]
    cache=stage.tree(cs,state['namespace'],state['blowup'],state['fold_bits'])
    h.require(cache['root'].hex()==state['root'],'terminal root binding')
    h.require(algebra.dot(cs,state['weights'].expanded())==f.canonical(state['claim']),'terminal residual')
    return True


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
                namespace=config['namespace'],root=child_root,parent=t.seed.hex(),weights=weights,claim=list(claim))


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
                root=proof['child_root'],parent=t.seed.hex(),weights=weights,claim=list(claim))


stage.start=start
stage.obligation=obligation
stage.close_terminal=close_terminal


def verify(proof,statement,parent,branches,claim,config,*,native=None,events=None):
    if events is None:events=[]
    adapter=closed._clone(closed._adapter,__name__+'._adapter')
    pcs=closed._clone(adapter.pcs,__name__+'._pcs')
    pcs.eqs=lambda point:Weights(Functional.equality(point),native,events)
    adapter.pcs=pcs;adapter.stage=stage;adapter.initial_obligation=initial_obligation
    return adapter.verify(proof,statement,parent,branches,claim,config,native=Backend())


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    p=argparse.ArgumentParser();p.add_argument('--proof',type=Path,required=True);p.add_argument('--statement',type=Path,required=True);a=p.parse_args()
    s=json.loads(a.statement.read_text());verify(json.loads(a.proof.read_text()),bytes.fromhex(s['statement']),bytes.fromhex(s['parent']),s['branches'],s['claim'],s['config'])
    print('PASS closed hybrid arithmetic; experimental security only.')
