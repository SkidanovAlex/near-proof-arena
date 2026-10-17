"""Account exact measured Ext8 call-proof bytes; no quantum-security claim."""
import argparse,hashlib,json,math
from pathlib import Path
import sha384_call_ext8_pcs as cp


def main():
    p=argparse.ArgumentParser();p.add_argument('--run',type=Path,action='append',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];read=lambda f:json.loads(f.read_text())
    expected=read(package/'results/ext8-node-batch/expected-use.json');calls=read(package/'results/ext8-linked-calls/calls.json');runs=[]
    for directory in a.run:
        report=read(directory/'report.json');proof=read(directory/'proof.json');statement=read(directory/'statement.json');wire=(directory/'proof.bin').read_bytes();q=report['queries']
        assert report['status']=='PASS' and report['fresh_conjunction_verified']
        assert len(wire)==report['call_proof_bytes'] and hashlib.sha256(wire).hexdigest()==report['proof_sha256']
        layout,st,binding,_=cp.compile_layout(statement,expected,calls,queries=q);ob=cp.g.verify(layout,binding,proof['gkr']);branches=cp.branches(statement,ob)
        breakdown=cp.codec.breakdown(proof['opening'],st,cp.parent(binding,proof['gkr']),branches,ob['private_claim'],queries=q)
        gkr_bytes=8+32*sum(sum(len(row) for row in layer['rounds'])+len(layer['inputs']) for layer in proof['gkr']['layers'])
        assert gkr_bytes+breakdown['total_bytes']==len(wire)
        sources=[s for s in breakdown['stages'] if s['kind']=='sources']
        assert len(sources)==2 and branches[0]['root']==branches[1]['root']
        geometry=cp.codec.stages(proof['opening'],st,cp.parent(binding,proof['gkr']),branches,ob['private_claim'],q)[0]
        src=[s for s in geometry if s['kind']=='sources'];assert len(src)==2
        # Equal committed geometry and query indices allow future shared
        # authentication; the current encoder still emits both source stages.
        assert all(src[0][key]==src[1][key] for key in ('root','context','half','indices','width'))
        duplicate=sources[1]['leaf_bytes']+sources[1]['sibling_bytes']
        runs.append(dict(**report,gkr_bytes=gkr_bytes,pcs_breakdown=breakdown,
            duplicated_source_authentication_bytes=duplicate,
            projected_mixed_bundle_if_shared=report['combined_proofs_calls_receipt_bytes']-duplicate,
            isolated_query_term_negative_log2=-q*math.log2(.75),
            isolated_batching_gkr_term_negative_log2=8*math.log2(cp.P)-math.log2(414)))
    output=dict(status='PASS',runs=runs,
        scope='Measured call proofs use Ext8; accompanying compression proof remains Q8/Ext4. Neither bundle certifies PQ128 or full recursion. Shared-source savings are exact duplicated-byte accounting, not an implemented codec or verified smaller proof.',
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [Path(__file__),Path(cp.__file__),package/'airbender/direct-wasm/test_sha384_call_ext8_pcs.py',package/'airbender/direct-wasm/verify_sha384_call_ext8_bundle.py']})
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps([dict(queries=r['queries'],call_bytes=r['call_proof_bytes'],mixed_bytes=r['combined_proofs_calls_receipt_bytes'],duplicated_source_bytes=r['duplicated_source_authentication_bytes'],projected_shared_mixed_bytes=r['projected_mixed_bundle_if_shared']) for r in runs],indent=2))

if __name__=='__main__':main()
