"""Replay complete Ext8 execution reduction from externally fixed spec/roots.
No witness, cached opening descriptor, or prover-supplied terminal claim is used.
This diagnostic transcript has no complete proximity/QROM security certificate.
"""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'generic-air'))
import pq384_ext8_reference as f
import pq384_ext8_auxiliary as aux
import pq384_ext8_local as local
import pq384_ext8_terminal_gkr as gkr
import pq384_ext8_weighted_codec as codec
from pq384_ext8_terminal_compile import compile_ext8_terminal
from pq384_ext8_input_weights import opening_branches
from pq384_primitives import Transcript,hash_parts,require
from reference import public_messages


def opening_parameters(reduction,spec,roots):
    require(type(reduction)is dict and set(reduction)=={'spec','source_roots','aux_roots','finals','local','gkr'},'reduction fields')
    require(reduction['spec']==spec and reduction['source_roots']==roots,'external statement binding')
    count=len(spec['air']['tables'])
    require(len(roots)==len(reduction['aux_roots'])==len(reduction['finals'])==len(reduction['local'])==count,'table counts')
    source_roots=[codec.p.hashread(r) for r in roots];ars=[codec.p.hashread(r) for r in reduction['aux_roots']]
    finals=[]
    for table,values in zip(spec['air']['tables'],reduction['finals']):
        require(len(values)==aux.layout(table)['finals'],'final count');finals.append([f.canonical(v) for v in values])
    st=hash_parts(b'ext8-execution-reduction-diagnostic-v1',json.dumps(spec,sort_keys=True).encode(),*source_roots)
    t=Transcript(st);alpha,gamma=local.draw(t,2)
    sends=receives=f.ONE
    for table,fs in zip(spec['air']['tables'],finals):
        for i,value in zip(aux.layout(table)['order'],fs):
            if table['interactions'][i]['send']:sends=f.mul(sends,value)
            else:receives=f.mul(receives,value)
    for bus,send,message in public_messages(spec['air'],spec['public']):
        fp=f.base(bus+1)
        for value in reversed(message):fp=f.add(f.base(value),f.mul(alpha,fp))
        factor=f.sub(gamma,fp)
        if send:sends=f.mul(sends,factor)
        else:receives=f.mul(receives,factor)
    require(sends==receives,'global bus balance')
    binding=hash_parts(b'ext8-packed-auxiliary-roots',*ars,gkr.vector_bytes([v for fs in finals for v in fs]))
    t.commit(b'ext8-all-auxiliary-data',binding)
    terminals=[local.verify(spec,t,ti,proof) for ti,proof in enumerate(reduction['local'])]
    rho=local.draw(t)[0];circuit=compile_ext8_terminal(spec,alpha,gamma,finals,terminals,rho)
    layout=gkr.layer_circuit(circuit);gp=reduction['gkr'];ob=gkr.verify(layout,t.seed,gp,f.ZERO)
    descriptors=opening_branches(spec,terminals,circuit,ob['private_weights'])
    branches=[]
    for b in descriptors:
        root=(roots if b['branch']==0 else reduction['aux_roots'])[b['table']]
        branches.append({**{k:v for k,v in b.items() if k not in ('table','branch')},'root':root})
    parent=hash_parts(b'ext8-after-gkr',t.seed,json.dumps(gp,sort_keys=True,separators=(',',':')).encode())
    return st,parent,branches,ob['private_claim']


def verify(reduction,wire,spec,roots,*,queries):
    params=opening_parameters(reduction,spec,roots)
    require(codec.verify(wire,*params,queries=queries),'weighted opening')
    return True


def main():
    p=argparse.ArgumentParser()
    for key in ('reduction','opening','statement'):p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--queries',type=int,required=True);p.add_argument('--compression-receipt',type=Path)
    a=p.parse_args();read=lambda x:json.loads(x.read_text());statement=read(a.statement)
    if a.compression_receipt:
        from verify_sha384_node_chunk import contract
        contract(statement,read(a.compression_receipt))
    verify(read(a.reduction),a.opening.read_bytes(),statement['spec'],statement['roots'],queries=a.queries)
    print('PASS complete Ext8 local/GKR/PCS reduction; external spec/roots; diagnostic security only.')

if __name__=='__main__':main()
