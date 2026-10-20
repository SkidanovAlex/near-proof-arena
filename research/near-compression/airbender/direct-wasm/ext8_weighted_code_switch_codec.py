"""Canonical sequential multiproof codec for the experimental switch adapter.
External schedule/branches determine all dimensions. Decoding authenticates
responses before deriving mixers and checks the final continuing obligation.
"""
import struct
import ext8_weighted_code_switch as a
import pq384_multiproof as mp
MAGIC=b'NP8WCS01'
MAX_BYTES=32*1024*1024


def process(data,proof,statement,parent,branches,claim,config,native=None):
    writing=proof is not None;out=bytearray();offset=0;seen={};groups=[];header=0
    if not writing:a.require(type(data)is bytes and len(data)<=MAX_BYTES,'switch codec cap')
    def transfer(n,value=None,metadata=True):
        nonlocal offset,header
        if metadata:header+=n
        if writing:
            a.require(type(value)is bytes and len(value)==n,'codec value shape');out.extend(value)
            a.require(len(out)<=MAX_BYTES,'switch codec cap');return value
        a.require(n>=0 and offset+n<=len(data),'truncated switch codec')
        value=data[offset:offset+n];offset+=n;return value
    def scalar(value=None):return list(a.f.canonical(struct.unpack('<8I',transfer(32,a.stage.extbytes(value) if writing else None))))
    def root(value=None):return transfer(48,a.pcs.hashread(value) if writing else None).hex()
    def quadratic(value=None):return [scalar(value[i] if writing else None) for i in range(3)]
    def group(kind,root_hex,context,count,indices,width,ops=None,base=False):
        position=len(out) if writing else offset
        key=(root_hex,context,count,tuple(indices),width,base)
        if key in seen:
            cached=seen[key]
            if writing:a.require(ops==cached,'conflicting shared switch source')
            groups.append(dict(kind=kind,offset=position,shared=True,leaf_bytes=0,sibling_bytes=0));return cached
        unique=mp.shape(count,indices);boundary=mp.boundary(count,indices);r=a.pcs.hashread(root_hex)
        if writing:
            leaves=[a.stage.h.field_words(op['leaf']) if base else a.stage.vector(op['values']) for op in ops]
            shared=mp.compress(r,context,count,indices,leaves,[[a.pcs.hashread(x) for x in op['path']] for op in ops])
        else:shared=None
        leaves=[transfer(width,shared['leaves'][i] if writing else None,False) for i in range(len(unique))]
        siblings=[transfer(48,shared['siblings'][i] if writing else None,False) for i in range(len(boundary))]
        leaves,paths=mp.expand(r,context,count,indices,dict(leaves=leaves,siblings=siblings))
        result=[]
        for leaf,path in zip(leaves,paths):
            values=list(struct.unpack('<'+'I'*(width//4),leaf))
            op=dict(path=[x.hex() for x in path])
            if base:op['leaf']=values
            else:op['values']=[list(a.f.canonical(values[i:i+8])) for i in range(0,len(values),8)]
            result.append(op)
        seen[key]=result;groups.append(dict(kind=kind,offset=position,shared=False,unique_leaves=len(unique),leaf_bytes=len(unique)*width,sibling_bytes=len(boundary)*48))
        return result
    a.require(transfer(8,MAGIC if writing else None)==MAGIC,'switch codec version')
    degrees,D,contexts,t,claim,namespace=a.start(statement,parent,branches,claim,config)
    reduction=[];u=[]
    for i in range(D.bit_length()-1):
        q=quadratic(proof['reduction'][i] if writing else None);r,_,claim=a.pcs.round_start(t,q,claim);u.append(r);reduction.append(q)
    betas=a.pcs.betas(branches,degrees,D,u);weights=a.pcs.eqs(u)
    expected=proof['first'] if writing else None
    q=quadratic(expected['quadratic'] if writing else None);r,claim=a.stage.round_step(t,q,claim)
    weights=(a.f.affine_fold if native is None else native.affine_fold)(weights,r)
    child=root(expected['child_root'] if writing else None);answer=scalar(expected['ood_answer'] if writing else None)
    preview=a.stage.h.Transcript(b'');preview.seed=t.seed
    a.stage.after_root(preview,child);indices=a.stage.after_answer(preview,answer,2*D,config['queries'])
    source=[]
    for j,(b,d,ctx) in enumerate(zip(branches,degrees,contexts)):
        source.append(group('packed-source',b['root'],ctx,2*d,[i%(2*d) for i in indices],8*a.pcs.lane_count(b),
                            [ops[j] for ops in expected['source_openings']] if writing else None,True))
    first=dict(quadratic=q,child_root=child,ood_answer=answer,source_openings=[[source[j][i] for j in range(len(source))] for i in range(len(indices))])
    state=a.initial_obligation(first,config,branches,degrees,D,contexts,t,weights,claim,betas,namespace,r,native=native)
    tail=[]
    for stage_index,step in enumerate(config['tail_steps']):
        cfg=a.stage.follow_config(state,step);t,weights,claim,N,count,omega=a.stage.start(cfg,state['weights'],state['claim'])
        expected=proof['tail'][stage_index] if writing else None;rounds=[];challenges=[]
        for i in range(cfg['fold_bits']):
            q=quadratic(expected['rounds'][i] if writing else None);r,claim=a.stage.round_step(t,q,claim);challenges.append(r);rounds.append(q)
            weights=(a.f.affine_fold if native is None else native.affine_fold)(weights,r)
        child=root(expected['child_root'] if writing else None);answer=scalar(expected['ood_answer'] if writing else None)
        z=a.stage.after_root(t,child);indices=a.stage.after_answer(t,answer,count,cfg['queries'])
        ctx=a.stage.context(cfg['namespace'],cfg['degree'],cfg['blowup'],cfg['fold_bits'])
        ops=group('scalar-coset',cfg['root'],ctx,count,indices,32*(1<<cfg['fold_bits']),expected['source_openings'] if writing else None)
        state=a.stage.obligation(cfg,t,weights,claim,child,z,answer,indices,ops,challenges,N,count,omega,native=native)
        tail.append(dict(rounds=rounds,child_root=child,ood_answer=answer,source_openings=ops))
    a.require(state['fold_bits']==0,'adapter terminal schedule')
    terminal=[scalar(proof['terminal'][i] if writing else None) for i in range(state['degree'])]
    a.stage.close_terminal(state,terminal)
    if not writing:a.require(offset==len(data),'trailing switch codec bytes')
    restored=dict(profile=a.PROFILE,reduction=reduction,first=first,tail=tail,terminal=terminal)
    detail=dict(header_and_terminal_bytes=header,groups=groups,total_bytes=header+sum(g['leaf_bytes']+g['sibling_bytes'] for g in groups))
    a.require(detail['total_bytes']==(len(out) if writing else len(data)),'switch codec accounting')
    return bytes(out) if writing else restored,detail


def encode(proof,statement,parent,branches,claim,config, *, native=None):
    a.verify(proof,statement,parent,branches,claim,config,native=native)
    return process(None,proof,statement,parent,branches,claim,config,native)[0]


def decode(data,statement,parent,branches,claim,config, *, native=None):
    return process(data,None,statement,parent,branches,claim,config,native)[0]


def breakdown(data,statement,parent,branches,claim,config, *, native=None):
    return process(data,None,statement,parent,branches,claim,config,native)[1]


if __name__=='__main__':
    import argparse,json
    from pathlib import Path
    from pq384_ext8_native import Kernel
    p=argparse.ArgumentParser();p.add_argument('--proof',type=Path,required=True);p.add_argument('--statement',type=Path,required=True);p.add_argument('--native-library',type=Path);x=p.parse_args()
    s=json.loads(x.statement.read_text());native=Kernel(x.native_library) if x.native_library else None
    decode(x.proof.read_bytes(),bytes.fromhex(s['statement']),bytes.fromhex(s['parent']),s['branches'],s['claim'],s['config'],native=native)
    print('PASS compact packed-root code-switch proof; diagnostic security only.')
