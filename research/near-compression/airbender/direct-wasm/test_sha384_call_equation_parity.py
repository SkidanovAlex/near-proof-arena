"""Compare every Python call descriptor with the Lean-defined generator."""
import argparse,gzip,hashlib,json,subprocess
from pathlib import Path
import sha384_call_pcs as cp


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    source=package/'results/ext8-linked-calls';read=lambda f:json.loads(f.read_text())
    st=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()));calls=read(source/'calls.json')
    receipt=read(package/'results/ext8-node-batch/expected-use.json');n=1<<st['spec']['log_rows'][3]
    fixture=out/'cases.json';fixture.write_bytes(gzip.decompress((package/'results/ext8-call-check/cases.json.gz').read_bytes()))
    positive=[c for c in read(fixture) if c['expected']]
    assert len(positive)==len(calls)
    for case,call in zip(positive,calls):
        assert bytes(case['message']).hex()==call['message_hex'] and case['ordinals']==call['ordinals']
        assert b''.join(w.to_bytes(8,'big') for w in case['final'])[:48].hex()==call['digest_hex']
    leanfile=out/'equations.json'
    result=subprocess.run(['lake','env','lean','--run','ExportSHA384CallEquations.lean',str(fixture),str(leanfile),str(n)],cwd=package,text=True,capture_output=True)
    (out/'lean.log').write_text(result.stdout+result.stderr);result.check_returncode()
    py=[[left,int(right is not None),right or 0,value] for left,right,value in cp.equations(st,receipt,calls)]
    lean=read(leanfile);assert py==lean,'descriptor generator divergence'
    assert all(0<=left<n*179 and (not flag or 0<=right<n*179) and 0<=value<65536 for left,flag,right,value in lean)
    report=dict(status='PASS',calls=len(calls),equations=len(lean),copy_equations=sum(e[1] for e in lean),
        constant_equations=sum(1-e[1] for e in lean),all_descriptor_slots_and_constants_match=True,
        row_count=n,private_capacity=n*256,equations_sha256=hashlib.sha256(leanfile.read_bytes()).hexdigest(),
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [Path(cp.__file__),package/'NearCompression/SHA384CallEquations.lean',package/'ExportSHA384CallEquations.lean',source/'calls.json']},
        scope='Exact2880-descriptor regression on retained12call batch, independently padded and word-decoded in Lean. General Lean descriptor semantics proved; arbitrary-input Python correspondence, residual batching, GKR compilation and cryptographic/QROM soundness are not established by this regression.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
