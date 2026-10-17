"""Extract the retained call GKR arithmetic path and replay the proved Lean checker."""
import argparse,copy,gzip,hashlib,json,subprocess
from pathlib import Path
import sha384_call_pcs as cp


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    source=package/'results/ext8-linked-calls';read=lambda f:json.loads(f.read_text())
    st=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()));calls=read(source/'calls.json')
    receipt=read(package/'results/ext8-node-batch/expected-use.json')
    proof=json.loads(gzip.decompress((package/'results/ext8-call-pcs/proof.json.gz').read_bytes()))['gkr']
    g=cp.g;layout,_,binding,_=cp.compile_layout(st,receipt,calls)
    expected=g.verify(layout,binding,proof)
    claim=g.ZERO;t=g.begin(layout,binding,claim)
    n=(len(layout['layers'][-1])-1).bit_length()
    queries=[([g.base((layout['root']>>i)&1) for i in range(n)],g.ONE)]
    cases=[]
    for layer,part in zip(range(len(layout['layers'])-1,-1,-1),proof['layers']):
        gates=layout['layers'][layer];weights=g.output_weights(len(gates),queries)
        prev=layout['input_size'] if layer==0 else len(layout['layers'][layer-1]);m=(prev-1).bit_length()
        initial=claim;point=[]
        for row in part['rounds']:
            coeff=[g.ext(x) for x in row]
            assert g.add(g.poly(coeff,g.ZERO),g.poly(coeff,g.ONE))==claim
            g.commit(t,coeff);r=g.draw(t);point.append(r);claim=g.poly(coeff,r)
        left,right=map(g.ext,part['inputs'])
        assert g.wiring(gates,weights,point[:m],point[m:],left,right)==claim
        g.commit(t,[left,right]);gamma=g.draw(t)
        cases.append(dict(m=m,initial=initial,rounds=part['rounds'],point=point,a=left,b=right,gamma=gamma,
            gates=[[*gate,w] for gate,w in zip(gates,weights)],expected=True))
        claim=g.add(left,g.mul(gamma,right));queries=[(point[:m],g.ONE),(point[m:],gamma)]
    assert g.obligation(layout,queries,claim)==expected,'extracted terminal obligation changed'
    positives=len(cases)
    for mutation in ('initial','coefficient','degree','challenge','input','shape'):
        bad=copy.deepcopy(cases[0]);bad['expected']=False
        if mutation=='initial':bad['initial']=g.add(bad['initial'],g.ONE)
        elif mutation=='coefficient':bad['rounds'][0][0]=g.add(bad['rounds'][0][0],g.ONE)
        elif mutation=='degree':bad['rounds'][0].append(g.ONE)
        elif mutation=='challenge':bad['point'][0]=g.add(bad['point'][0],g.ONE)
        elif mutation=='input':bad['a']=g.add(bad['a'],g.ONE)
        else:bad['point'].pop()
        cases.append(bad)
    fixture=out/'messages.json';fixture.write_text(json.dumps(cases,separators=(',',':')))
    run=subprocess.run(['lake','env','lean','--run','CheckGKRMessages.lean',str(fixture)],cwd=package,text=True,capture_output=True,timeout=120)
    (out/'lean.log').write_text(run.stdout+run.stderr);run.check_returncode()
    report=dict(status='PASS',layers=positives,rounds=sum(len(c['rounds']) for c in cases[:positives]),
        negative_cases=len(cases)-positives,terminal_obligation_exactly_matches_verifier=True,
        fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest(),
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in
          [Path(__file__),package/'CheckGKRMessages.lean',package/'NearCompression/GKRMessageCheck.lean',Path(g.__file__)]},
        scope='Actual transcript-derived challenges, weighted gates and arithmetic messages replay through a proved finite Lean checker. Tape functions certify this path only; they do not establish a causal prover strategy across challenge paths. Transcript derivation, cross-layer query binding and PCS/QROM remain separate obligations; no PQ128 claim.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
