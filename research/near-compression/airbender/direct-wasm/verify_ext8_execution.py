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
import ext8_terminal_profiles as profiles
import ext8_commitment_profiles as commitments


def reduction_prefix(reduction,spec,roots,*,terminal_profile="baseline",commitment_profile="separate"):
    require(type(reduction)is dict and set(reduction)=={'spec','source_roots','aux_roots','finals','local','gkr'},'reduction fields')
    require(reduction['spec']==spec and reduction['source_roots']==roots,'external statement binding')
    count=len(spec['air']['tables'])
    require(len(roots)==len(reduction['aux_roots'])==len(reduction['finals'])==len(reduction['local'])==count,'table counts')
    source_roots=[codec.p.hashread(r) for r in roots];ars=[codec.p.hashread(r) for r in reduction['aux_roots']]
    commitments.check_roots(spec,roots,reduction['aux_roots'],commitment_profile)
    finals=[]
    for table,values in zip(spec['air']['tables'],reduction['finals']):
        require(len(values)==aux.layout(table)['finals'],'final count');finals.append([f.canonical(v) for v in values])
    st=commitments.statement(spec,source_roots,commitment_profile)
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
    circuit=profiles.apply(circuit,terminal_profile)
    layout=gkr.layer_circuit(circuit)
    return st,t,terminals,circuit,layout


def opening_parameters(reduction,spec,roots,*,terminal_profile="baseline",commitment_profile="separate"):
    return _opening_parameters(reduction,spec,roots,reduction_prefix(reduction,spec,roots,terminal_profile=terminal_profile,commitment_profile=commitment_profile),commitment_profile=commitment_profile)


def _opening_parameters(reduction,spec,roots,checked_prefix,*,commitment_profile="separate"):
    st,t,terminals,circuit,layout=checked_prefix
    gp=reduction['gkr'];ob=gkr.verify(layout,t.seed,gp,f.ZERO)
    descriptors=opening_branches(spec,terminals,circuit,ob['private_weights'])
    branches=commitments.bind_branches(spec,descriptors,roots,reduction['aux_roots'],commitment_profile)
    parent=hash_parts(b'ext8-after-gkr',t.seed,json.dumps(gp,sort_keys=True,separators=(',',':')).encode())
    return st,parent,branches,ob['private_claim']


def verify(reduction,wire,spec,roots,*,queries,terminal_profile="baseline",commitment_profile="separate"):
    params=opening_parameters(reduction,spec,roots,terminal_profile=terminal_profile,commitment_profile=commitment_profile)
    require(codec.verify(wire,*params,queries=queries),'weighted opening')
    return True


def main():
    p=argparse.ArgumentParser()
    for key in ('reduction','opening','statement'):p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--queries',type=int,required=True);p.add_argument('--compression-receipt',type=Path)
    p.add_argument("--terminal-profile",choices=profiles.PROFILES,default="baseline")
    p.add_argument("--commitment-profile",choices=commitments.PROFILES,default="separate")
    a=p.parse_args();read=lambda x:json.loads(x.read_text());statement=read(a.statement)
    if a.compression_receipt:
        from verify_sha384_node_chunk import contract
        contract(statement,read(a.compression_receipt))
    verify(read(a.reduction),a.opening.read_bytes(),statement['spec'],statement['roots'],queries=a.queries,terminal_profile=a.terminal_profile,commitment_profile=a.commitment_profile)
    print('PASS complete Ext8 local/GKR/PCS reduction; external spec/roots; diagnostic security only.')

if __name__=='__main__':main()
