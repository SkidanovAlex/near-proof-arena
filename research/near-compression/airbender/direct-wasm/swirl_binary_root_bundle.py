"""Complete version2 diagnostic bundle; old version remains supported separately."""
import gzip,hashlib,json,sys
from pathlib import Path
from prove_swirl_binary_root import OUT as GKR,SOURCE,context
from swirl_binary_transcript import pack_v2,unpack_v2
from swirl_bundle_codec import encode_gkr,decode_gkr
from swirl_bundle import verify_blob,tests
OUT=SOURCE.parent/'binary-root-bundle'


def main():
    OUT.mkdir(exist_ok=True)
    if sys.argv[1:]==['--verify-saved']:
        print('PASS',verify_blob((OUT/'proof.bin').read_bytes(),'fresh',root=True,typed=True));return
    assert not sys.argv[1:]
    layout,*_=context()
    proof=json.loads(gzip.decompress((GKR/'proof.json.gz').read_bytes()))
    encoded=encode_gkr(layout,proof);assert decode_gkr(layout,encoded)==proof
    sections=[(SOURCE/'prefix.bin').read_bytes(),encoded,
        gzip.decompress((GKR/'stacking.proof.gz').read_bytes()),gzip.decompress((GKR/'whir.proof.gz').read_bytes())]
    blob=pack_v2(sections);assert pack_v2(unpack_v2(blob))==blob
    (OUT/'proof.bin').write_bytes(blob)
    hidden=[]
    try:
        for p in [Path('/tmp/nearproof-root-split-witness/native.proof'),Path('/tmp/nearproof-witness-internal.proof'),GKR/'proof.json.gz']:
            if p.exists():
                dest=p.with_name(p.name+'.v2-backup');assert not dest.exists();p.rename(dest);hidden.append((p,dest))
        sizes=verify_blob(blob,'positive',root=True,typed=True)
        rejected=tests(blob,layout,root=True,typed=True)
        old=(SOURCE.parent/'root-bundle-codec/proof.bin').read_bytes()
        for label,data,typed in [('old_relabelled_v2',b'NPBND002'+old[8:],True),('v2_relabelled_old',b'NPBND001'+blob[8:],False)]:
            try:verify_blob(data,label,root=True,typed=typed)
            except (ValueError,AssertionError):rejected.append(label)
            else:raise AssertionError('cross-version accepted')
        verify_blob(blob,'restored-positive',root=True,typed=True)
    finally:
        for p,dest in reversed(hidden):dest.rename(p)
    report=dict(status='BINARY_TRANSCRIPT_ROOT_BUNDLE_VERIFIED',bytes=sizes,negative_checks=rejected,
        original_proofs_and_saved_gkr_json_unavailable=True,sha256=hashlib.sha256(blob).hexdigest(),
        limitations=['Versioned protocol experiment; Ext4 diagnostic, not PQ128.',
                    'Native prefix must be verified under fixed key before controls are used.',
                    'Generic root fixture, not full NEAR or a circuit proving compressed-bundle verification.',
                    'No Lean codec, transcript or complete composition theorem.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':main()
