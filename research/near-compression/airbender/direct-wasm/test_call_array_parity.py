"""Replay the actual compiler's coefficient accumulation through proved Lean code."""
import argparse,gzip,hashlib,json,subprocess
from pathlib import Path
import sha384_call_pcs as cp
from pq384_primitives import Transcript,hash_parts


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    source=package/'results/ext8-linked-calls';read=lambda f:json.loads(f.read_text())
    st=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()));calls=read(source/'calls.json')
    receipt=read(package/'results/ext8-node-batch/expected-use.json');capacity=(1<<st['spec']['log_rows'][3])*256
    eq=cp.equations(st,receipt,calls)
    seed=hash_parts(cp.PROFILE,cp.canonical(receipt),cp.canonical(calls),cp.canonical(st['spec']),bytes.fromhex(st['roots'][3]))
    point=[tuple(x) for x in Transcript(seed).draw(b'call-equations-after-use-root',(len(eq)-1).bit_length(),4)[0]]
    weights=cp.g.eqs(point)[:len(eq)]
    scenarios=[('retained',eq,weights,capacity),('aliases',[(0,0,0),(1,None,7),(1,1,0),(0,1,3),(1,None,2)],
        [cp.g.ZERO,cp.g.ONE,(2,3,4,5),(6,7,8,9),cp.g.ONE],2)]
    reports=[]
    for name,eqs,ws,cap in scenarios:
        fixture=out/(name+'.json');output=out/(name+'-lean.json')
        fixture.write_text(json.dumps(dict(capacity=cap,equations=[[l,int(r is not None),r or 0,v] for l,r,v in eqs],weights=ws)))
        run=subprocess.run(['lake','env','lean','--run','ReplayCallArray.lean',str(fixture),str(output)],cwd=package,text=True,capture_output=True)
        (out/(name+'.log')).write_text(run.stdout+run.stderr);run.check_returncode()
        result=read(output);coeff,claim=cp.compile_coefficients(eqs,ws,cap)
        assert len(result)==4
        assert all(result[k][0]==[c[k] for c in coeff] and result[k][1]==claim[k] for k in range(4))
        reports.append(dict(name=name,equations=len(eqs),capacity=cap,all_coefficients_and_claim_match=True,
            replay_sha256=hashlib.sha256(output.read_bytes()).hexdigest()))
    # The compiler refactor must preserve the existing proof and its exact wire encoding.
    proofdir=package/'results/ext8-call-pcs'
    proof=json.loads(gzip.decompress((proofdir/'proof.json.gz').read_bytes()))
    wire=(proofdir/'proof.bin').read_bytes()
    assert cp.encode(proof,st,receipt,calls)==wire
    report=dict(status='PASS',scenarios=reports,retained_proof_verifies_and_encoding_unchanged=True,
        proof_sha256=hashlib.sha256(wire).hexdigest(),
        scope='Coordinatewise concrete parity for base-constant accumulation, including aliases and zero/unit weights. General Lean array functional theorem is audited. This does not prove arbitrary Python correspondence, GKR lowering, Fiat-Shamir/QROM soundness or full recursion.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
