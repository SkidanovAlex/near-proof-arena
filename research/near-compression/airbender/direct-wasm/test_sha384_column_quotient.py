import argparse,copy,hashlib,json,os,subprocess,sys
from pathlib import Path
import verify_sha384_column_quotient as verifier

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--original-spec',required=True);p.add_argument('--proof-dir',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_global_bus_codec as codec
    original=json.loads(Path(a.original_spec).read_text());out=Path(a.proof_dir);statement=json.loads((out/'statement.json').read_text());proof=json.loads((out/'proof.json').read_text());roots=[bytes.fromhex(r) for r in statement['roots']]
    spec=verifier.derived_spec(original);assert statement['spec']==spec;assert verifier.verify(proof,original,roots)
    wire=codec.encode(proof,spec,roots);assert codec.decode(wire,spec,roots)==proof;(out/'proof.bin').write_bytes(wire)
    env=os.environ.copy();env['PYTHONPATH']=os.pathsep.join([str(Path(__file__).parent),a.reference_dir])
    fresh=subprocess.run([sys.executable,str(Path(verifier.__file__)),'--reference-dir',a.reference_dir,'--original-spec',a.original_spec,'--proof-dir',a.proof_dir,'--binary'],env=env,check=True,capture_output=True,text=True)
    negatives=0
    def reject(value=proof,config=original,rs=roots):
        nonlocal negatives
        try:verifier.verify(value,config,rs)
        except (ValueError,AssertionError,KeyError,IndexError):negatives+=1
        else:raise AssertionError('mutation accepted')
    for idx in (0,len(original['public'])-1):
        bad=copy.deepcopy(original);bad['public'][idx]^=1;reject(config=bad)
    bad=copy.deepcopy(original);bad['air']['tables'][0]['constraints'][0]=['c',1];reject(config=bad)
    bad=copy.deepcopy(original);bad['air']['tables'][1]['interactions']=[];reject(config=bad)
    bad=copy.deepcopy(proof);bad['tables']=bad['tables'][::-1];reject(value=bad)
    bad=copy.deepcopy(roots);bad[0]=bytes([bad[0][0]^1])+bad[0][1:];reject(rs=bad)
    report=dict(status='PASS',proof_bytes=len(wire),proof_sha256=hashlib.sha256(wire).hexdigest(),
        baseline_bytes=1508054,saving_bytes=1508054-len(wire),negative_checks=negatives,fresh_verifier=fresh.stdout.strip(),
        original_public_and_constraints_preserved_via_substitution=True,scope='Diagnostic proof; original AIR derived by mandatory deterministic quotient, generic semantic refinement separately proved in Lean')
    (out/'quotient-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
