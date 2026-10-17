"""Measured root-split diagnostic bundle using root-specific verified inputs."""
import gzip,hashlib,json,sys
from pathlib import Path
from prove_swirl_root_public_dag import SOURCE,OUT as GKR,context
from swirl_bundle_codec import pack,unpack,encode_gkr,decode_gkr
from swirl_bundle import verify_blob,tests
OUT=SOURCE.parent/'root-bundle-codec'
CONT=SOURCE.parent/'root-split-continuation'


def main():
    OUT.mkdir(exist_ok=True)
    if sys.argv[1:]==['--verify-saved']:
        print('PASS',verify_blob((OUT/'proof.bin').read_bytes(),'fresh',root=True));return
    assert not sys.argv[1:]
    layout,*_=context()
    proof=json.loads(gzip.decompress((GKR/'proof.json.gz').read_bytes()))
    raw=encode_gkr(layout,proof);assert decode_gkr(layout,raw)==proof
    sections=[(SOURCE/'prefix.bin').read_bytes(),raw,
        gzip.decompress((CONT/'stacking.proof.gz').read_bytes()),gzip.decompress((CONT/'whir.proof.gz').read_bytes())]
    blob=pack(sections);assert pack(unpack(blob))==blob
    (OUT/'proof.bin').write_bytes(blob)
    hidden=[]
    try:
        for p in [Path('/tmp/nearproof-root-split-witness/native.proof'),Path('/tmp/nearproof-witness-internal.proof'),GKR/'proof.json.gz']:
            if p.exists():
                dest=p.with_name(p.name+'.root-bundle-backup');assert not dest.exists();p.rename(dest);hidden.append((p,dest))
        sizes=verify_blob(blob,'positive',root=True)
        rejected=tests(blob,layout,root=True)
        verify_blob(blob,'restored-positive',root=True)
    finally:
        for p,dest in reversed(hidden):dest.rename(p)
    report=dict(status='ROOT_FRAMED_DIAGNOSTIC_BUNDLE_VERIFIED',bytes=sizes,negative_checks=rejected,
        original_proofs_and_saved_gkr_json_unavailable_during_tests=True,sha256=hashlib.sha256(blob).hexdigest(),
        limitations=['Generic cached-VK recursive root fixture, not production RootProver or full NEAR.',
                    'Ext4/upstream diagnostic security, not PQ128.',
                    'No Lean codec/compiler/composition or QROM theorem.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':main()
