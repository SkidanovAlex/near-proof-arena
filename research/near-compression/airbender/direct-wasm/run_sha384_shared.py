"""Commit both actual caller inputs before producing a joint shared-node proof."""
import argparse,hashlib,json,os,subprocess,sys,time
from pathlib import Path
from verify_sha384_shared import PROFILE,canonical,verify,fixed_contract

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--rs-binary',required=True);p.add_argument('--folded-library',required=True);p.add_argument('--fft-library',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    from run_pq384_global_bus import choose_packing
    from packed_claim_handoff import packing_context
    import pq384_compact_gkr_bus_codec as codec
    src=Path(a.fixture_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);spec=json.loads((src/'spec.json').read_text());receipt=out/'expected-inputs.json'
    assert not receipt.exists(),'fresh output required; caller receipts cannot be overwritten'
    expected={'profile':PROFILE,'air_sha384':hashlib.sha384(canonical(spec['air'])).hexdigest(),'inputs':[]}
    for c in range(2):
        rows=json.loads((src/f'source-{4+c:02d}-rows.json').read_text())['rows'];message=(src/f'message-{c}.bin').read_bytes();fixed=json.loads((src/f'fixed-{c}.json').read_text());fixed_contract(267,fixed)
        assert len(message)==267 and rows==[[(v>>j)&1 for v in message for j in range(8)],[0]*2136] and all(message[i]==v for i,v in fixed)
        packing=choose_packing(1,2136);cache=out/f'external-input-{c}-cache';inp=out/f'external-input-{c}-commit.json';res=out/f'external-input-{c}-result.json'
        inp.write_bytes(canonical({'rows':rows,'packing':packing,'indices':[],'cache_directory':str(cache)}));subprocess.run([a.rs_binary,str(inp),str(res)],check=True,capture_output=True)
        manifest=json.loads((cache/'manifest.json').read_text());expected['inputs'].append({'declared_length':267,'fixed_framing':fixed,'input_root':manifest['root_hex'],'input_context_hex':packing_context(1,2136,packing).hex()})
    receipt.write_bytes(canonical(expected));started=time.perf_counter()
    command=[sys.executable,str(Path(a.reference_dir)/'run_pq384_gkr_bus.py'),'--reference-dir',a.reference_dir,'--spec',str(src/'spec.json'),'--source-directory',str(src),'--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(out)]
    with (out/'prover.log').open('w') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    statement=json.loads((out/'statement.json').read_text());proof=json.loads((out/'proof.json').read_text());roots=[bytes.fromhex(r) for r in statement['roots']];wire=codec.encode(proof,statement['spec'],roots);(out/'proof.bin').write_bytes(wire)
    assert verify(wire,statement,expected)
    env=os.environ.copy();env['PYTHONPATH']=a.reference_dir
    checked=subprocess.run([sys.executable,str(Path(__file__).with_name('verify_sha384_shared.py')),str(out/'proof.bin'),str(out/'statement.json'),str(receipt),'--reference-dir',a.reference_dir],env=env,capture_output=True,text=True,check=True);(out/'fresh-verifier.log').write_text(checked.stdout+checked.stderr)
    report=dict(status='PASS',profile=PROFILE,proof_profile=proof['profile'],codec='NPGC compact GKR v1',proof_bytes_including_six_source_roots=len(wire),public_fixed_width_bytes=384,external_receipt_json_bytes=receipt.stat().st_size,proof_public_and_receipt_bytes=len(wire)+384+receipt.stat().st_size,external_roots_created_before_prover=True,fresh_process_verify=True,elapsed_after_external_commits=time.perf_counter()-started,binary_sha256=hashlib.sha256(wire).hexdigest(),receipt_sha256=hashlib.sha256(receipt.read_bytes()).hexdigest(),logical_blocks=6,unique_compressions=5,padded_core_row_savings=0,scope='Shared compression diagnostic; no full recursive verifier, zero knowledge, QROM or128-bit security claim. Exact natural AIR checks are separate from randomized fingerprint proof soundness.')
    (out/'shared-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
