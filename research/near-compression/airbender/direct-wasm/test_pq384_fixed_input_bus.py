"""Fixed cap is caller configuration, bound before challenges; no security claim."""
import argparse
import copy
import json
import sys
from pathlib import Path


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--reference-dir',required=True)
    ap.add_argument('--fixture',type=Path,required=True)
    ap.add_argument('--baseline',type=Path,required=True)
    ap.add_argument('--input-log',type=int,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();sys.path.insert(0,args.reference_dir)
    import pq384_gkr_bus as bus
    def load(path):
        s=json.loads((path/'statement.json').read_text())
        return json.loads((path/'proof.json').read_text()),s['spec'],[bytes.fromhex(r) for r in s['roots']]
    proof,spec,roots=load(args.fixture);old,oldspec,oldroots=load(args.baseline)
    assert spec==oldspec and roots==oldroots
    assert bus.verify(proof,spec,roots,input_log=args.input_log)
    assert bus.verify(old,oldspec,oldroots)
    assert len(proof['gkr']['layers'][-1]['rounds'])==2*args.input_log
    assert bus.statement(oldspec).hex()==json.loads((args.baseline/'prover-report.json').read_text())['canonical_statement_digest']
    assert len({bus.statement(spec),bus.statement(spec,input_log=args.input_log),bus.statement(spec,input_log=args.input_log+1)})==3
    rejected=[]
    def reject(name,fn):
        try:fn()
        except ValueError:rejected.append(name)
        else:raise AssertionError('accepted '+name)
    for cap in (None,args.input_log-1,args.input_log+1):
        reject('changed cap '+str(cap),lambda cap=cap:bus.verify(proof,spec,roots,input_log=cap))
    for cap in (True,0,26,-1):
        reject('invalid cap '+str(cap),lambda cap=cap:bus.statement(spec,input_log=cap))
    reject('old proof fixed verifier',lambda:bus.verify(old,spec,roots,input_log=args.input_log))
    retagged=copy.deepcopy(old);retagged['profile']=bus.FIXED_PROFILE
    reject('retagged old proof',lambda:bus.verify(retagged,spec,roots,input_log=args.input_log))
    injected=copy.deepcopy(proof);injected['input_log']=args.input_log
    reject('proof selected cap field',lambda:bus.verify(injected,spec,roots,input_log=args.input_log))
    mutated=copy.deepcopy(proof);mutated['tables'][0][0][0][0]=(mutated['tables'][0][0][0][0]+1)%2013265921
    reject('changed constraint message',lambda:bus.verify(mutated,spec,roots,input_log=args.input_log))
    report=dict(status='PASS',profile=proof['profile'],trusted_input_log=args.input_log,
                rejected=rejected,baseline_statement_digest_unchanged=True,same_source_roots=True,
                auxiliary_roots_changed=proof['aux_roots']!=old['aux_roots'],
                scope='Integrated AIR/GKR/weighted PCS JSON proof; compact codec and prepared-request frontend not yet extended to this profile; Q8/Ext4 only.')
    args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
