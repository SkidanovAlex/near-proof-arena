"""Measure only a completed full execution capture and verified call conjunction."""
import argparse,gzip,hashlib,json,subprocess,sys,tempfile
from pathlib import Path


def main():
    p=argparse.ArgumentParser()
    for key in ('capture','statement','receipt','calls','call-proof','config','output'):p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--call-queries',type=int,required=True);a=p.parse_args()
    report=json.loads((a.capture/'report.json').read_text());assert report['status']=='PASS' and report['fresh_execution_verified']
    a.output.mkdir(exist_ok=True,parents=True)
    with tempfile.TemporaryDirectory(prefix='switch-bundle-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_ext8.rs'),'-o',str(lib)],check=True)
        cmd=[sys.executable,str(Path(__file__).with_name('verify_ext8_switch_bundle.py')),'--call-queries',str(a.call_queries),'--native-library',str(lib),'--compression-proof',str(a.capture/'compression.bin')]
        for key in ('statement','receipt','calls','call-proof','config'):cmd+=['--'+key,str(getattr(a,key.replace('-','_')))]
        fresh=subprocess.run(cmd,text=True,capture_output=True);(a.output/'fresh-conjunction.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    compression=(a.capture/'compression.bin').stat().st_size;assert compression==report['compression_envelope_bytes']
    sizes=dict(compression_envelope_bytes=compression,call_proof_bytes=a.call_proof.stat().st_size,receipt_bytes=a.receipt.stat().st_size,calls_bytes=a.calls.stat().st_size)
    total=sum(sizes.values())
    output=dict(status='PASS',**sizes,combined_bytes=total,under_300000_bytes=total<300000,fresh_conjunction_verified=True,
        scope='Actual diagnostic code-switch compression and unchanged call proof. External static AIR/spec/schedule excluded; no NEAR1Pgas, source-extraction/proximity/QROM/PQ128 certificate.',
        files={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [a.capture/'compression.bin',a.capture/'report.json',a.statement,a.receipt,a.calls,a.call_proof,a.config]})
    (a.output/'report.json').write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))

if __name__=='__main__':main()
