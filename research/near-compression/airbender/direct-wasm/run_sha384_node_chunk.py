"""Full diagnostic proof for a compression chunk with an already fixed use receipt."""
import argparse,hashlib,json,os,subprocess,sys,time
from pathlib import Path
from verify_sha384_node_chunk import canonical,contract,verify,PROFILE

def main():
    p=argparse.ArgumentParser();p.add_argument('--reference-dir',required=True);p.add_argument('--fixture-directory',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--rs-binary',required=True);p.add_argument('--folded-library',required=True);p.add_argument('--fft-library',required=True);a=p.parse_args();sys.path.append(a.reference_dir)
    import pq384_compact_gkr_bus_codec as codec
    src=Path(a.fixture_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);assert not (out/'expected-use.json').exists(),'fresh proof output required'
    receipt_raw=(src/'expected-use.json').read_bytes();expected=json.loads(receipt_raw);(out/'expected-use.json').write_bytes(receipt_raw)
    started=time.perf_counter()
    command=[sys.executable,str(Path(a.reference_dir)/'run_pq384_gkr_bus.py'),'--reference-dir',a.reference_dir,'--spec',str(src/'spec.json'),'--source-directory',str(src),'--rs-binary',a.rs_binary,'--folded-library',a.folded_library,'--fft-library',a.fft_library,'--output-dir',str(out)]
    with (out/'prover.log').open('w') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    proof_seconds=time.perf_counter()-started
    statement=json.loads((out/'statement.json').read_text());proof=json.loads((out/'proof.json').read_text());roots=[bytes.fromhex(r) for r in statement['roots']];assert contract(statement,expected)
    wire=codec.encode(proof,statement['spec'],roots);(out/'proof.bin').write_bytes(wire);assert verify(wire,statement,expected)
    checked=subprocess.run([sys.executable,str(Path(__file__).with_name('verify_sha384_node_chunk.py')),str(out/'proof.bin'),str(out/'statement.json'),str(out/'expected-use.json'),'--reference-dir',a.reference_dir],text=True,capture_output=True,check=True)
    (out/'fresh-verifier.log').write_text(checked.stdout+checked.stderr)
    cfg=json.loads((src/'config.json').read_text());cells=json.loads((src/'checks.json').read_text())['source_cells'];selection=json.loads((src/'selection.json').read_text())
    report=dict(status='PASS',profile=PROFILE,proof_profile=proof['profile'],codec='NPGC compact GKR v1',proof_bytes_including_four_source_roots=len(wire),public_fixed_width_bytes=0,external_receipt_json_bytes=len(receipt_raw),receipt_context_bytes=len(bytes.fromhex(expected['use_context_hex'])),receipt_external_root_bytes=48,proof_public_and_receipt_bytes=len(wire)+len(receipt_raw),canonical_air_json_bytes=len(canonical(statement['spec']['air'])),canonical_air_digest_binding_in_receipt=True,source_cells=cells,source_shapes=[[1<<l,t['width']] for l,t in zip(statement['spec']['log_rows'],statement['spec']['air']['tables'])],global_base=cfg['base'],unique_nodes=cfg['count'],declared_unique_call_steps=len(cfg['uses']),original_occurrence_steps=selection['original_occurrence_step_uses'],fanout_bits=cfg['fanout_bits'],prior_witness_and_external_commit_work_excluded=True,prover_runner_seconds=proof_seconds,elapsed_after_fixed_external_receipt=time.perf_counter()-started,fresh_process_verify=True,binary_sha256=hashlib.sha256(wire).hexdigest(),receipt_sha256=hashlib.sha256(receipt_raw).hexdigest(),scope='Compression-record component only. Q8/BabyBearExt4 diagnostic, no quantum128/QROM/proximity certification. Ordered use root fixed externally; call-chain, IV/padding/digest provenance, cross-chunk coverage and aggregation remain open. Canonical static AIR/spec external to payload; four source commitments are included.')
    (out/'chunk-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
