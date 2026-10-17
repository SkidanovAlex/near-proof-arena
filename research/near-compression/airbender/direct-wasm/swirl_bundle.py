"""Build/replay the complete diagnostic transport from decoded bundle sections.

Verifier uses fixed source-pinned VK/DAG and protocol implementation. No original
proof, saved GKR JSON, source openings or witness matrices are verifier inputs.
"""
import gzip,json,os,struct,subprocess,sys,hashlib
from pathlib import Path
from prove_swirl_prefix_dag import BASE,OUT as GKR
from verify_swirl_prefix_dag import public_context
from prepare_swirl_prefix_continuation import main as prepare
from swirl_bundle_codec import pack,unpack,encode_gkr,decode_gkr,P
REPO=Path('/tmp/nearproof-openvm')
OUT=BASE/'bundle-codec'


def native(name,env,label,output_dir=OUT):
    result=subprocess.run(['cargo','test','--locked','--profile','fast','-p','openvm-recursion-circuit',
        'tests::'+name,'--','--exact','--nocapture'],cwd=REPO,env=env,capture_output=True,text=True)
    (output_dir/(label+'.log')).write_text(result.stdout+result.stderr)
    if result.returncode:raise ValueError('native rejection: '+label)


def verify_blob(data,label='replay',root=False):
    output_dir=BASE/'root-bundle-codec' if root else OUT
    output_dir.mkdir(exist_ok=True)
    dag_path=BASE/'root-split-witness/dag.jsonl.gz' if root else None
    prefix,gkr_bytes,stack,whir=unpack(data)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()=='e74f9b1ee868c42776faf821b8b9f2e8829a7f68'
    env=os.environ.copy()
    for key in ('NEARPROOF_GKR_BINDING','NEARPROOF_WEIGHTED_WHIR','NEARPROOF_NATIVE_CAPTURE','NEARPROOF_PREFIX_ONLY','NEARPROOF_EXPORT_PREFIX','NEARPROOF_ROOT_SPLIT','NEARPROOF_SOURCE_PROOF','NEARPROOF_WITNESS_DIR'):env.pop(key,None)
    if root:env['NEARPROOF_ROOT_SPLIT']='1'
    env['RAYON_NUM_THREADS']='4';env['NEARPROOF_PREFIX_ONLY']='/tmp/nearproof-retained-prefix.bin'
    Path('/tmp/nearproof-retained-prefix.bin').write_bytes(prefix)
    Path('/tmp/nearproof-weighted-stacking.proof').write_bytes(stack)
    Path('/tmp/nearproof-weighted-whir.proof').write_bytes(whir)
    native('nearproof_opening_free_prefix',env,label+'-prefix',output_dir)
    c=json.loads(Path('/tmp/nearproof-opening-free-controls.json').read_text())
    log=Path('/tmp/nearproof-opening-free-prefix-log.txt').read_bytes()
    shapes=json.loads(Path('/tmp/nearproof-prefix-trace-shapes.json').read_text())
    layouts=json.loads(Path('/tmp/nearproof-prefix-layouts.json').read_text())
    layout,*_=public_context(c,log,dag_path)
    proof=decode_gkr(layout,gkr_bytes)
    assert encode_gkr(layout,proof)==gkr_bytes
    Path('/tmp/nearproof-reconstructed-witness').mkdir(exist_ok=True)
    prepare(proof,c,log,shapes,layouts,write_outputs=False,dag_path=dag_path)
    env['NEARPROOF_GKR_BINDING']='/tmp/nearproof-prefix-gkr-binding.bin'
    native('nearproof_replay_weighted_whir',env,label+'-continuation',output_dir)
    return dict(prefix=len(prefix),gkr=len(gkr_bytes),stacking=len(stack),whir=len(whir),framing=24,total=len(data))


def build():
    layout,*_=public_context()
    proof=json.loads(gzip.decompress((GKR/'proof.json.gz').read_bytes()))
    encoded=encode_gkr(layout,proof);assert decode_gkr(layout,encoded)==proof
    sections=[(BASE/'prefix-codec/prefix.bin').read_bytes(),encoded,
        gzip.decompress((BASE/'prefix-continuation/stacking.proof.gz').read_bytes()),
        gzip.decompress((BASE/'prefix-continuation/whir.proof.gz').read_bytes())]
    blob=pack(sections);assert pack(unpack(blob))==blob
    (OUT/'proof.bin').write_bytes(blob)
    return blob,layout


def tests(blob,layout,root=False):
    framing=[('truncated_header',blob[:23]),('truncated_body',blob[:-1]),('trailing_byte',blob+b'\0'),
             ('wrong_version',b'X'+blob[1:]),('zero_section',blob[:8]+b'\0'*4+blob[12:]),
             ('oversized_length',blob[:8]+b'\xff'*4+blob[12:])]
    rejected=[]
    for label,data in framing:
        try:unpack(data)
        except ValueError:rejected.append(label)
        else:raise AssertionError(label)
    gkr=unpack(blob)[1]
    for label,data in [('gkr_truncation',gkr[:-1]),('gkr_trailing',gkr+b'\0'),('gkr_noncanonical',struct.pack('<I',P)+gkr[4:])]:
        try:decode_gkr(layout,data)
        except ValueError:rejected.append(label)
        else:raise AssertionError(label)
    # Same-shape payload mutations must fail the actual arithmetic/authentication path.
    for section,name in enumerate(['prefix','gkr','stacking','whir']):
        pieces=unpack(blob);changed=bytearray(pieces[section])
        # Prefix offset8 is the first commitment byte; other tail bytes are field payload.
        offset=8 if section==0 else (0 if section==1 else len(changed)-1)
        changed[offset]^=1;pieces[section]=bytes(changed)
        try:verify_blob(pack(pieces),'mutated-'+name,root=root)
        except (ValueError,AssertionError):rejected.append('mutated_'+name)
        else:raise AssertionError('mutation accepted: '+name)
    return rejected


def main():
    OUT.mkdir(exist_ok=True)
    if sys.argv[1:]==['--verify-saved']:
        print('PASS',verify_blob((OUT/'proof.bin').read_bytes(),'fresh'));return
    assert not sys.argv[1:]
    blob,layout=build()
    # Check the decoder uses the bundle, even when original proof and GKR JSON are unavailable.
    hidden=[]
    try:
        for p in [Path('/tmp/nearproof-witness-internal.proof'),GKR/'proof.json.gz']:
            if p.exists():
                dest=p.with_name(p.name+'.bundle-test-backup');assert not dest.exists();p.rename(dest);hidden.append((p,dest))
        sizes=verify_blob(blob,'positive')
        rejected=tests(blob,layout)
        verify_blob(blob,'restored-positive')
    finally:
        for p,dest in reversed(hidden):dest.rename(p)
    report=dict(status='FRAMED_DIAGNOSTIC_BUNDLE_VERIFIED',bytes=sizes,negative_checks=rejected,
        original_proof_and_saved_gkr_json_unavailable_during_tests=True,
        sha256=hashlib.sha256(blob).hexdigest(),
        limitations=['Pinned internal recursive fixture; preprocessed AIRs unsupported by prefix codec.',
                    'Native test-harness verifier; no Lean codec/composition or QROM theorem.',
                    'Ext4/upstream diagnostic settings, not PQ128, root geometry or full NEAR.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(report)


if __name__=='__main__':main()
