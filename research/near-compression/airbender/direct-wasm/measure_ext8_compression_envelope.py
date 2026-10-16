"""Measure a completed Ext8 compression capture plus same-root Ext8 call proof.
Never substitutes an Ext4 compression proof or trusts a partial run report.
"""
import argparse,gzip,hashlib,json,subprocess,sys
from pathlib import Path
import ext8_execution_codec as codec
from verify_sha384_node_chunk import contract


def main():
    p=argparse.ArgumentParser()
    for key in ('capture','prover-report','statement','receipt','call-proof','calls','output'):p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--queries',type=int,required=True);a=p.parse_args()
    read=lambda path:json.loads(path.read_text())
    report=read(a.prover_report);assert report['status']=='PASS' and report['weighted_pcs']['verified'] and report['weighted_pcs']['queries']==a.queries
    statement,receipt=read(a.statement),read(a.receipt);contract(statement,receipt)
    reduction=read(a.capture/'reduction.json');opening=(a.capture/'proof.bin').read_bytes()
    wire=codec.encode(reduction,opening,statement['spec'],statement['roots'],queries=a.queries)
    assert codec.decode(wire,statement['spec'],statement['roots'],queries=a.queries)==(reduction,opening)
    a.output.mkdir(parents=True,exist_ok=True);(a.output/'compression.bin').write_bytes(wire)
    command=[sys.executable,str(Path(__file__).with_name('verify_sha384_call_ext8_bundle.py')),
        '--queries',str(a.queries),'--compression-format','ext8','--call-proof',str(a.call_proof),
        '--compression-proof',str(a.output/'compression.bin'),'--statement',str(a.statement),'--receipt',str(a.receipt),'--calls',str(a.calls)]
    fresh=subprocess.run(command,text=True,capture_output=True);(a.output/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    params=codec.v.opening_parameters(reduction,statement['spec'],statement['roots'])
    op=codec.v.codec.decode(opening,*params,queries=a.queries)
    detail=codec.v.codec.breakdown(op,*params,queries=a.queries)
    # This compression has one branch per source/auxiliary table: no aliasing.
    stages=codec.v.codec.stages(op,*params,a.queries)[0]
    keys=[codec.v.codec.source_key(s) for s in stages if s['kind']=='sources']
    assert len(keys)==len(set(keys)) and detail['total_bytes']==len(opening)
    total=len(wire)+a.call_proof.stat().st_size+a.receipt.stat().st_size+a.calls.stat().st_size
    output=dict(status='PASS',queries=a.queries,compression_extension_degree=8,call_extension_degree=8,
        compression_envelope_bytes=len(wire),compression_opening_bytes=len(opening),compression_reduction_bytes=len(wire)-len(opening),
        call_proof_bytes=a.call_proof.stat().st_size,receipt_bytes=a.receipt.stat().st_size,calls_bytes=a.calls.stat().st_size,
        combined_bytes=total,under_300000_bytes=total<300000,fresh_conjunction_verified=True,pcs_breakdown=detail,
        scope='Actual all-Ext8 SHA384 node/call diagnostic, externally fixed operands and receipt; static AIR/spec excluded. Not a full recursive verifier or full NEAR1Pgas proof. No PQ128/QROM/proximity certificate.',
        files={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in [Path(__file__),Path(codec.__file__),a.prover_report,a.statement,a.receipt,a.call_proof,a.calls,a.capture/'reduction.json',a.capture/'proof.bin']})
    for name,path in [('statement',a.statement),('reduction',a.capture/'reduction.json'),('prover-report',a.prover_report)]:
        (a.output/(name+'.json.gz')).write_bytes(gzip.compress(path.read_bytes(),mtime=0))
    (a.output/'report.json').write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))

if __name__=='__main__':main()
