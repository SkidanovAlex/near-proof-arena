"""Require exact retained proof parity before reporting native batch timings."""
import argparse, hashlib, json
from pathlib import Path


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--reference',type=Path,required=True)
    p.add_argument('--native',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    read=lambda directory,name:json.loads((directory/name).read_text())
    old,new=read(a.reference,'report.json'),read(a.native,'report.json')
    oc,nc=read(a.reference,'chunk-report.json'),read(a.native,'chunk-report.json')
    assert old['status']==new['status']==oc['status']==nc['status']=='PASS'
    assert new['gkr_backend']=='native-ext4' and new['gkr_library_sha256']
    assert old['source_hashes']==new['source_hashes']
    assert old['statement_sha256']==new['statement_sha256']
    assert old['proof_sha256']==new['proof_sha256']
    wire=(a.native/'proof.bin').read_bytes()
    assert wire==(a.reference/'proof.bin').read_bytes()
    assert (a.native/'expected-use.json').read_bytes()==(a.reference/'expected-use.json').read_bytes()
    assert nc['fresh_process_verify'] and (a.native/'fresh-verifier.log').read_text().startswith('PASS')
    timings=dict(reference=old['timing'],native=new['timing'])
    report=dict(status='PASS',binary_sha256=hashlib.sha256(wire).hexdigest(),proof_bytes=len(wire),
        exact_proof_json_and_binary_parity=True,exact_statement_and_receipt_parity=True,
        fresh_process_verify=True,native_library_sha256=new['gkr_library_sha256'],timings=timings,
        gkr_pcs_speedup=old['timing']['gkr_and_weighted_pcs']/new['timing']['gkr_and_weighted_pcs'],
        reference_pipeline_seconds=oc['elapsed_after_fixed_external_receipt'],
        native_pipeline_seconds=nc['elapsed_after_fixed_external_receipt'],
        scope='One retained 24-node SHA384 batch; same Q8/Ext4 diagnostic proof. Single-run timings include PCS; no full-DAG throughput extrapolation, Rust refinement or security certification.')
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
