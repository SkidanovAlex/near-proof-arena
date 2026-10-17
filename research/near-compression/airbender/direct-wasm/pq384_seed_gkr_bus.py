"""New all-zerocheck -> random terminal batch -> GKR -> weighted PCS profile.

Canonical AIR/config digest and fixed-width public/shape encoding bind the
statement. All roots and fresh auxiliaries precede constraints. No disclosed
current/next/final-column vectors and no abandoned opening obligation.
Diagnostic only: weighted joint proximity/RBR/QROM and GKR composition pending.
"""
import json,sys
import pq384_global_bus as old
import pq384_seed_gkr as gkr
import pq384_derived_weight_joint as pcs
from pq384_terminal_compile import compile_terminal
from pq384_terminal_input_weights import branch_lanes
from pq384_table_air import AirTranscript
from pq384_primitives import require,hash_parts,u64,field_words
from packed_claim_handoff import canonical_ext as ext
from native_folded_v2 import compile_weighted,NativeTable,library
from verify_whir_toy import ZERO,ONE,add,poly
from pq384_native_fft import NativeFFT
from pq384_source_cache import SourceCache
import pq384_native_shift as ns
import pq384_shift as shift
PROFILE='near-pq384-seed-gkr-bus-v1'
aux=old.aux;validate=old.validate;initialize_aux=old.initialize_aux


def empty_aux_root(spec,ti,st):
    require(type(st)is bytes and len(st)==48,'new-profile statement digest required')
    return old.empty_aux_root(spec,ti,st)


def configure(air):
    """Trusted setup/configuration, independent of a proof and public values.

    A deployed recursive verifier fixes this AIR digest and compiler semantics.
    This reference computes them once from caller-supplied trusted canonical AIR;
    setup hashing is separately accounted for, never claimed free at runtime.
    """
    import copy
    old.schema(air)
    digest=hash_parts(b'seed-gkr-static-air-config-v1',json.dumps(air,sort_keys=True,separators=(',',':')).encode(),gkr.CONFIG)
    return dict(air=copy.deepcopy(air),digest=digest,compiler=gkr.CONFIG)


def statement(spec,config):
    old.validate(spec);require(spec['terminal_degree']==1,'constant terminal only')
    require(config['air']==spec['air'] and config['compiler']==gkr.CONFIG and type(config['digest'])is bytes and len(config['digest'])==48,'trusted AIR/compiler config')
    shape=b''.join(u64(v) for key in ('log_rows','source_packings','aux_packings') for v in spec[key])
    return hash_parts(PROFILE.encode(),config['digest'],u64(len(spec['public'])),field_words(spec['public']),u64(len(spec['log_rows'])),shape,u64(1))


def begin(spec,roots,config):
    old.check_roots(roots,len(spec['air']['tables']));st=statement(spec,config);t=AirTranscript(st);t.statement_digest=st
    t.t.commit(b'all-source-commitments',u64(len(roots))+b''.join(roots))
    return st,t,t.draw(1,True)[0],t.draw(1,True)[0]


def constraint_prove(spec,t,alpha,gamma,ti,rows,coords,finals,lib):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti];degree=old.algebra.table_degree(table,spec['air']['numPub'])
    sw=table['width'];aw=4*aux.layout(table)['aux_columns']
    require(len(rows)==len(coords)==1<<n and all(len(r)==sw and len(c)==aw for r,c in zip(rows,coords)),'trace shape')
    mixing,tau=old.table_start(t,ti,n);program=compile_weighted(table,spec['public'],alpha,gamma,[ext(x) for x in finals],mixing,old)
    rounds=[];point=[];claim=ZERO
    with NativeTable([r+c for r,c in zip(rows,coords)],program,tau,lib) as state:
        for _ in range(n):
            cs=shift.interpolate(state.values(degree+2));require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'invalid trace constraints')
            rounds.append(cs);t.commit_ext(cs);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r);state.fold(r)
        current,nxt=ns.terminal(state)
    return rounds,dict(point=point,mixing=mixing,tau=tau,claim=claim),(current,nxt)


def constraint_verify(spec,t,ti,rounds):
    table=spec['air']['tables'][ti];n=spec['log_rows'][ti];degree=old.algebra.table_degree(table,spec['air']['numPub']);mixing,tau=old.table_start(t,ti,n)
    require(isinstance(rounds,list) and len(rounds)==n,'constraint rounds');point=[];claim=ZERO
    for cs in rounds:
        require(len(cs)==degree+2,'constraint degree');cs=[ext(x) for x in cs]
        require(add(poly(cs,ZERO),poly(cs,ONE))==claim,'constraint endpoint');t.commit_ext(cs);r=t.draw(1,True)[0];point.append(r);claim=poly(cs,r)
    return dict(point=point,mixing=mixing,tau=tau,claim=claim)


def terminal_layout(spec,t,alpha,gamma,finals,terminals):
    t.t.commit(b'all-constraint-proofs-complete',u64(len(terminals)));rho=t.draw(1,True)[0]
    circuit=compile_terminal(spec,alpha,gamma,finals,terminals,rho)
    binding=hash_parts(b'gkr-after-all-constraints',t.seed)
    return circuit,gkr.layer_circuit(circuit),binding


def opening_arguments(spec,roots,ars,terminals,circuit,obligation):
    blocks={x['table']:x for x in circuit['input_blocks']};branches=[]
    for ti,table in enumerate(spec['air']['tables']):
        sw=table['width'];aw=4*aux.layout(table)['aux_columns']
        for branch,width,offset,key,root in ((0,sw,0,'source_packings',roots[ti]),(1,aw,sw,'aux_packings',ars[ti])):
            if not width:continue
            packing=spec[key][ti]
            branches.append(dict(root=root.hex(),log_rows=spec['log_rows'][ti],width=width,packing=packing,row_point=terminals[ti]['point'],
                lanes=branch_lanes(blocks[ti],offset,width,packing,obligation['private_weights'])))
    return branches


def opening_parent(binding,seed):
    require(type(seed)is bytes and len(seed)==48,'final GKR transcript seed')
    return hash_parts(b'weighted-pcs-after-seed-gkr',binding,seed)


def finish_prove(spec,roots,ars,finals,st,t,alpha,gamma,rounds,terminals,private_rows,caches,native):
    circuit,layout,binding=terminal_layout(spec,t,alpha,gamma,finals,terminals)
    private=[ZERO]*circuit['private_input_capacity']
    for block in circuit['input_blocks']:
        current,nxt=private_rows[block['table']];offset=block['offset'];W=block['column_capacity']
        private[offset:offset+len(current)]=current;private[offset+W:offset+W+len(nxt)]=nxt
    gp,ob=gkr.prove(layout,binding,private)
    branches=opening_arguments(spec,roots,ars,terminals,circuit,ob)
    opening=pcs.prove(caches,native,st,opening_parent(binding,ob['transcript_seed']),branches,ob['private_claim'])
    return dict(profile=PROFILE,aux_roots=[r.hex() for r in ars],finals=finals,tables=rounds,gkr=gp,opening=opening)


def verify_local(proof,spec,roots,config):
    require(set(proof)=={'profile','aux_roots','finals','tables','gkr','opening'} and proof['profile']==PROFILE,'proof fields')
    st,t,alpha,gamma=begin(spec,roots,config);ars=[pcs.decode_hash(x) for x in proof['aux_roots']];initialize_aux(t,spec,ars,proof['finals'])
    require(len(proof['tables'])==len(roots),'table count')
    terminals=[constraint_verify(spec,t,ti,rounds) for ti,rounds in enumerate(proof['tables'])]
    circuit,layout,binding=terminal_layout(spec,t,alpha,gamma,proof['finals'],terminals)
    ob=gkr.verify(layout,binding,proof['gkr']);branches=opening_arguments(spec,roots,ars,terminals,circuit,ob)
    pcs.verify(proof['opening'],st,opening_parent(binding,ob['transcript_seed']),branches,ob['private_claim'])
    return alpha,gamma


def verify(proof,spec,roots,config):
    alpha,gamma=verify_local(proof,spec,roots,config)
    require(old.global_fingerprint_balance(spec,proof['finals'],alpha,gamma),'randomized bus fingerprint product')
    return True

if __name__=='__main__':
    from pathlib import Path
    p=json.loads(Path(sys.argv[1]).read_text());s=json.loads(Path(sys.argv[2]).read_text())
    assert verify(p,s['spec'],[bytes.fromhex(x) for x in s['roots']],configure(s['spec']['air']))
    print('PASS: GKR and mandatory weighted opening diagnostic; security not certified')
