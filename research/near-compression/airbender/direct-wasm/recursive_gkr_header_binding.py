"""Derive PCS headers from complete old-profile GKR proofs and trusted statements.

No caller-supplied PCS header or claimed private functional is accepted. GKR,
constraint transcript, compiler and bus checks still run natively. This module
does not relabel the new seed/derived-weight profile and is not a recursive
proof of the native checks. Application input receipts remain trusted config.
"""
import argparse,copy,json,sys,time
from pathlib import Path
import recursive_fold_trace as fold


def derive(proof,statement):
    import pq384_gkr_bus_codec as codec
    bus=codec.bus
    fold.require(type(statement)is dict and set(statement)=={'spec','roots'},'trusted statement shape')
    spec=statement['spec'];roots=[bytes.fromhex(r) for r in statement['roots']]
    fold.require(type(proof)is dict and set(proof)=={'profile','aux_roots','finals','tables','gkr','opening'} and proof['profile']==bus.PROFILE,'original GKR profile only')
    bus.validate(spec)
    st,alpha,gamma,ars,terminals,circuit,layout,binding,_,_=codec.prefix(spec,roots,proof)
    obligation=bus.gkr.verify(layout,binding,proof['gkr'])
    branches=bus.opening_arguments(spec,roots,ars,terminals,circuit,obligation)
    fold.require(bus.old.global_fingerprint_balance(spec,proof['finals'],alpha,gamma),'bus fingerprint product')
    return {'statement':st.hex(),'parent':bus.opening_parent(binding,proof['gkr']).hex(),'branches':branches,'claim':list(obligation['private_claim'])}


def bind_sessions(sessions,proofs,statements):
    fold.require(len(sessions)==len(proofs)==len(statements)>=2,'complete component count')
    headers=[]
    for session,proof,statement in zip(sessions,proofs,statements):
        h=derive(proof,statement)
        fold.require(fold.canonical(fold.header(session))==fold.canonical(h),'GKR-derived PCS header')
        fold.require(fold.canonical(session['proof'])==fold.canonical(proof['opening']),'exact original PCS proof')
        headers.append(h)
    return headers


def verify_conjunction(conjunction,artifact,proofs,statements):
    import recursive_conjunction_gkr as g
    headers=bind_sessions(artifact['fold']['sessions'],proofs,statements)
    return g.verify(conjunction,artifact,headers)


def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--results-dir',type=Path,required=True);p.add_argument('--source-trace',type=Path,required=True);p.add_argument('--conjunction-directory',type=Path);p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args();sys.path.insert(0,a.reference_dir)
    specs=[json.loads((a.results_dir/name/'statement.json').read_text()) for name in ('sha384-direct','sha384-committed-gkr')]
    proofs=[json.loads(Path(path).read_text()) for path in ('/tmp/near-sha384-direct-proof/proof.json','/tmp/near-sha384-committed-gkr-proof/proof.json')]
    artifact=json.loads(a.source_trace.read_text());start=time.monotonic();headers=bind_sessions(artifact['fold']['sessions'],proofs,specs);elapsed=time.monotonic()-start
    cases=[]
    def reject(name,change):
        altered=copy.deepcopy(proofs);change(altered)
        try:bind_sessions(artifact['fold']['sessions'],altered,specs)
        except (ValueError,AssertionError,IndexError,KeyError):cases.append(name)
        else:raise AssertionError('accepted '+name)
    reject('missing component',lambda b:b.pop())
    reject('wrong GKR input claim',lambda b:b[0]['gkr']['layers'][0]['inputs'][0].__setitem__(0,(b[0]['gkr']['layers'][0]['inputs'][0][0]+1)%2013265921))
    reject('omitted GKR layer',lambda b:b[0]['gkr']['layers'].pop())
    reject('substituted PCS proof',lambda b:b[0]['opening']['queries'].pop())
    reject('seed profile relabel forbidden',lambda b:b[0].__setitem__('profile','near-pq384-seed-gkr-bus-v1'))
    full=False
    if a.conjunction_directory:
        c=json.loads((a.conjunction_directory/'proof.json').read_text());fold.require(verify_conjunction(c,artifact,proofs,specs),'derived-header conjunction');full=True
    a.output_directory.mkdir(parents=True,exist_ok=True);(a.output_directory/'derived-headers.json').write_bytes(fold.canonical(headers))
    report={'status':'PASS','components':len(proofs),'header_bytes':len(fold.canonical(headers)),'derive_seconds':elapsed,'negative_cases':cases,'conjunction_verified_with_derived_headers':full,'limits':['PCS headers derived from actual constraint transcript, exact terminal compiler, native final GKR wiring/functional verification and bus product checks.','No caller-supplied PCS header or private claim remains in this interface.','Trusted component statements/public input receipts still application supplied; original GKR and hash checks are native, not recursively proved.','Expanded original-profile proof inputs used; seed migration uses different interfaces and is explicitly rejected here.']}
    (a.output_directory/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
