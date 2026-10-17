"""Opt-in base auxiliary/packed PCS prover with a checked pre-PCS checkpoint."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys
import test_ext8_execution_reduction as execution
import pq384_ext8_auxiliary_base as fast
import pq384_ext8_packed_prover as packed
import verify_ext8_execution as verifier


def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--checkpoint-dir',type=Path,required=True);parser.add_argument('--statement',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    a,rest=parser.parse_known_args();st=json.loads(a.statement.read_text());n=len(st['spec']['air']['tables'])
    assert '--terminal-profile' in rest and rest[rest.index('--terminal-profile')+1]=='affine-v1'
    assert '--commitment-profile' not in rest or rest[rest.index('--commitment-profile')+1]=='separate'
    a.checkpoint_dir.mkdir(parents=True,exist_ok=True);local={};captured_gkr=[];roots=[];observed=[]
    original_source=execution.pcs.Source;original_local=execution.local.prove;original_gkr=execution.gkr.prove
    def source(*args,**kwargs):
        cache=original_source(*args,**kwargs);roots.append(cache.root.hex());observed.append(cache);return cache
    def local_prove(spec,t,alpha,gamma,ti,rows,coordinates,finals,lib):
        result=original_local(spec,t,alpha,gamma,ti,rows,coordinates,finals,lib)
        assert ti not in local
        local[ti]=(result[0],finals)
        return result
    def gkr_prove(*args,**kwargs):
        result=original_gkr(*args,**kwargs);captured_gkr.append(result[0]);return result
    def prove(caches,native,statement,parent,branches,claim,*,queries):
        assert len(roots)==2*n and roots[:n]==st['roots'] and set(local)==set(range(n)) and len(captured_gkr)==1
        reduction=dict(spec=st['spec'],source_roots=roots[:n],aux_roots=roots[n:],
            local=[local[i][0] for i in range(n)],finals=[local[i][1] for i in range(n)],gkr=captured_gkr[0])
        parameters=verifier.opening_parameters(reduction,st['spec'],roots[:n],terminal_profile='affine-v1')
        assert parameters[0]==statement and parameters[1]==parent and canonical(parameters[2:])==canonical((branches,claim))
        raw=canonical(reduction);(a.checkpoint_dir/'reduction.json.gz').write_bytes(gzip.compress(raw,mtime=0))
        opening=dict(statement=statement.hex(),parent=parent.hex(),branches=branches,claim=claim,queries=queries,
                     cache_indices=[observed.index(cache) for cache in caches])
        (a.checkpoint_dir/'opening.json').write_bytes(canonical(opening))
        (a.checkpoint_dir/'status.json').write_text(json.dumps(dict(status='LOCAL_GKR_AND_OPENING_PARAMETERS_CHECKED_PCS_PENDING',
            reduction_sha256=hashlib.sha256(raw).hexdigest(),opening_sha256=hashlib.sha256(canonical(opening)).hexdigest(),
            scope='Checked local/GKR reduction and exact PCS obligation, not a complete proof.'),indent=2)+'\n')
        print('Checked reduction checkpoint saved; starting packed PCS',flush=True)
        return packed.prove(caches,native,statement,parent,branches,claim,queries=queries)
    execution.aux.generate=fast.generate
    execution.local.prove=local_prove;execution.gkr.prove=gkr_prove
    execution.pcs.Source=source;execution.pcs.prove=prove
    sys.argv=[execution.__file__,'--statement',str(a.statement),'--output',str(a.output),*rest]
    execution.main()
    report=json.loads(a.output.read_text());report['witness_generator']='base-source-evaluation/packed-input-reduction'
    report['execution_adapter_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.output.write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
