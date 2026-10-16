"""Canonical Lean-export fixture, separate-process verifier, linkage mutations."""
import argparse,copy,json,os,subprocess,sys,time
from pathlib import Path


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True)
    ap.add_argument('--fixture',required=True);ap.add_argument('--output-dir',required=True)
    a=ap.parse_args();sys.path.append(a.reference_dir)
    import pq384_table_air as air
    from pq384_primitives import P
    f=json.loads(Path(a.fixture).read_text());spec={k:f[k] for k in ('air','table_index','public')}
    spec.update(log_rows=3,packing=16)
    root=air.source_commitment(f['rows'],spec);start=time.perf_counter()
    proof=air.prove(spec,root,f['rows']);assert air.verify_table_local(proof,spec,root)
    out=Path(a.output_dir);out.mkdir(parents=True,exist_ok=True)
    artifact=out/'table-proof.json';artifact.write_text(json.dumps(dict(spec=spec,root=root.hex(),proof=proof)))
    env=os.environ.copy();env['PYTHONPATH']=a.reference_dir
    result=subprocess.run([sys.executable,str(Path(air.__file__)),str(artifact)],env=env,
                          check=True,capture_output=True,text=True)
    rejects=0
    def reject(p=proof,s=spec,r=root):
        nonlocal rejects
        try:air.verify_table_local(p,s,r)
        except (ValueError,KeyError,TypeError,IndexError):rejects+=1
        else:raise AssertionError('invalid proof accepted')
    for key in ['current_evals','next_evals']:
        p=copy.deepcopy(proof);p['shift_reduction'][key][0][0]=(p['shift_reduction'][key][0][0]+1)%P;reject(p)
    p=copy.deepcopy(proof);p['column_claims'][0][0]=(p['column_claims'][0][0]+1)%P;reject(p)
    p=copy.deepcopy(proof);p['constraint_rounds'][0][0][0]=(p['constraint_rounds'][0][0][0]+1)%P;reject(p)
    p=copy.deepcopy(proof);p['shift_reduction']['rounds'][0][0][0]=(p['shift_reduction']['rounds'][0][0][0]+1)%P;reject(p)
    s=copy.deepcopy(spec);s['public'][0]=(s['public'][0]+1)%P;reject(s=s)
    s=copy.deepcopy(spec);s['air']['tables'][0]['constraints'][0]=['c',0];reject(s=s)
    reject(r=bytes([root[0]^1])+root[1:])
    # Reprove PCS under a wrong parent branch, preserving root/claims/point.
    statement,t,mixing,tau=air.begin(spec,root);point=[]
    for encoded in proof['constraint_rounds']:
        t.commit_ext(encoded);point.append(t.draw(1,True)[0])
    at=air.shift.verify(proof['shift_reduction'],point,len(f['rows'][0]),t,proof['column_claims'])
    args=air.handoff(spec,root,statement,t,at,proof['column_claims']);args['parent_binding']=b'wrong enclosing branch'
    p=copy.deepcopy(proof);p['opening']=air.pcs.prove(f['rows'],**args);reject(p)
    # A freshly committed/proved invalid trace must fail AIR, despite valid PCS.
    changed=copy.deepcopy(f['rows']);changed[2][0]=(changed[2][0]+1)%P
    changed_root=air.source_commitment(changed,spec)
    changed_proof=air.prove(spec,changed_root,changed)
    reject(changed_proof,spec,changed_root)
    report=dict(status='PASS',scope='Canonical AIR table-local only; buses not checked',
        source_fixture=str(Path(a.fixture).resolve()),degree=air.validate(spec)[1],rows=8,
        width=len(f['rows'][0]),negative_checks=rejects,verifier=result.stdout.strip(),
        elapsed_seconds=time.perf_counter()-start,artifact_bytes=artifact.stat().st_size,
        limits=['Q8 diagnostic Ext4; no claimed 128-bit or QROM security','No cross-table natural bus balance'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
