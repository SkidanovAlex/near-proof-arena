"""Cross-layer replay, using the already retained arithmetic records and layout."""
import argparse,copy,gzip,hashlib,json,subprocess
from pathlib import Path
import sha384_call_pcs as cp


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    messages=package/'results/call-gkr-messages/messages.json.gz'
    capture=package/'results/call-layer-certificates/case-0.json.gz'
    records=[c for c in json.loads(gzip.decompress(messages.read_bytes())) if c['expected']]
    bundle=json.loads(gzip.decompress(capture.read_bytes()));layers=bundle['layout']['layers']
    assert len(records)==len(layers)==14
    source=package/'results/ext8-linked-calls'
    st=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()))
    calls=json.loads((source/'calls.json').read_text());receipt=json.loads((package/'results/ext8-node-batch/expected-use.json').read_text())
    layout,_,_,_=cp.compile_layout(st,receipt,calls)
    assert json.loads(json.dumps(layout))==bundle['layout'],'retained layer layout changed'
    original=dict(records=records,layers=layers,expected=True)
    cases=[original];labels=[]
    for mutation in ('gamma','next-claim','next-gate-order','layer-wiring','missing-layer','extra-layer','empty-path'):
        bad=copy.deepcopy(original);bad['expected']=False
        if mutation=='gamma':bad['records'][0]['gamma']=cp.g.add(tuple(bad['records'][0]['gamma']),cp.g.ONE)
        elif mutation=='next-claim':bad['records'][1]['initial']=cp.g.add(tuple(bad['records'][1]['initial']),cp.g.ONE)
        elif mutation=='next-gate-order':bad['records'][1]['gates'][0],bad['records'][1]['gates'][1]=bad['records'][1]['gates'][1],bad['records'][1]['gates'][0]
        elif mutation=='layer-wiring':bad['layers'][-2][1][0]='mul' if bad['layers'][-2][1][0]!='mul' else 'add'
        elif mutation=='missing-layer':bad['records'].pop()
        elif mutation=='extra-layer':bad['records'].append(copy.deepcopy(bad['records'][-1]))
        else:bad['records']=[]
        cases.append(bad);labels.append(mutation)
    fixture=out/'paths.json';fixture.write_text(json.dumps(cases,separators=(',',':')))
    run=subprocess.run(['lake','env','lean','--run','CheckGKRPath.lean',str(fixture)],cwd=package,text=True,capture_output=True,timeout=120)
    (out/'lean.log').write_text(run.stdout+run.stderr);run.check_returncode()
    report=dict(status='PASS',layers=len(records),accepted_paths=1,rejected_cases=labels,
        fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest(),
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in
          [Path(__file__),package/'CheckGKRPath.lean',package/'NearCompression/GKRPathMessageCheck.lean',messages,capture]},
        scope='The retained 14-layer path passes the proved Lean checker, including adjacent query weights, claim links and circuit-depth alignment. Theorem yields evaluated verifier path for supplied history-indexed functions. Tape replay establishes one finite path, not causal transcript/Fiat-Shamir behavior across sampled paths or PCS/QROM soundness. Root-query binding is a separate interface.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
