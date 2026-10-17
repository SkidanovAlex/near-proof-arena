"""Commit the caller's actual input first, then produce and verify the component."""
import argparse,hashlib,json,os,subprocess,sys,time
from pathlib import Path
from verify_sha384_committed import PROFILE,canonical,verify

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--rs-binary',required=True);p.add_argument('--folded-library',required=True);p.add_argument('--fft-library',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    from run_pq384_global_bus import choose_packing
    from packed_claim_handoff import packing_context
    import pq384_global_bus_codec as codec
    src=Path(a.fixture_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);spec=json.loads((src/'spec.json').read_text());inputrows=json.loads((src/'source-02-rows.json').read_text())['rows'];message=(src/'message.bin').read_bytes();fixed=json.loads((src/'fixed-framing.json').read_text())
    assert len(message)==376 and len(inputrows)==2 and all(len(r)==3008 and all(v in(0,1) for v in r) for r in inputrows)
    assert inputrows[0]==[(b>>i)&1 for b in message for i in range(8)]
    assert len({i for i,v in fixed})==len(fixed) and all(type(i)is int and 0<=i<len(message) and type(v)is int and 0<=v<256 and message[i]==v for i,v in fixed)
    packing=choose_packing(1,3008);cache=out/'external-input-cache';inp=out/'external-input-commit.json';res=out/'external-input-result.json'
    assert not (out/'expected-input.json').exists(),'use a fresh output directory; do not replace caller input receipt'
    inp.write_bytes(canonical({'rows':inputrows,'packing':packing,'indices':[],'cache_directory':str(cache)}));subprocess.run([a.rs_binary,str(inp),str(res)],check=True,capture_output=True)
    manifest=json.loads((cache/'manifest.json').read_text());expected={'profile':PROFILE,'declared_length':376,'air_sha384':hashlib.sha384(canonical(spec['air'])).hexdigest(),'input_root':manifest['root_hex'],'input_context_hex':packing_context(1,3008,packing).hex()}
    receipt=out/'expected-input.json';receipt.write_bytes(canonical(expected))
    started=time.perf_counter();command=[sys.executable,str(Path(a.reference_dir)/'run_pq384_global_bus.py'),'--reference-dir',a.reference_dir,'--spec',str(src/'spec.json'),'--source-directory',str(src),'--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(out)]
    completed=subprocess.run(command,capture_output=True,text=True);(out/'prover.log').write_text(completed.stdout+completed.stderr);assert completed.returncode==0,completed.stderr
    statement=json.loads((out/'statement.json').read_text());proof=json.loads((out/'proof.json').read_text());roots=[bytes.fromhex(r) for r in statement['roots']];wire=codec.encode(proof,statement['spec'],roots);(out/'proof.bin').write_bytes(wire)
    assert verify(wire,statement,expected)
    env=os.environ.copy();env['PYTHONPATH']=a.reference_dir
    checked=subprocess.run([sys.executable,str(Path(__file__).with_name('verify_sha384_committed.py')),str(out/'proof.bin'),str(out/'statement.json'),str(receipt),'--reference-dir',a.reference_dir],env=env,capture_output=True,text=True,check=True);(out/'fresh-verifier.log').write_text(checked.stdout+checked.stderr)
    report={'status':'PASS','profile':PROFILE,'proof_bytes_including_all_source_roots':len(wire),'public_fixed_width_bytes':352,'proof_plus_public_bytes':len(wire)+352,'external_receipt_json_bytes':receipt.stat().st_size,'proof_public_and_external_receipt_bytes':len(wire)+352+receipt.stat().st_size,'external_input_root_created_before_prover':True,'external_root_matches_actual_input_and_proof':True,'fresh_process_verify':True,'elapsed_after_external_commit':time.perf_counter()-started,'binary_sha256':hashlib.sha256(wire).hexdigest(),'receipt_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),'scope':'Committed-input framed SHA384 component. No recursive producer-to-input commitment routing; no QROM or128bitsecurity claim; new AIR semantic refinement pending.'}
    (out/'committed-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
