"""Encode and freshly verify a completed nibble compression proof capture.
Roots are carried by the proof; this exposes the boundary root for a future
recursive-call consumer, and does not claim to verify an application hash.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import ext8_execution_codec as codec


def read(path):
    raw=path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix=='.gz' else raw)


def verify(wire,spec,queries):
    assert spec['public']==[] and len(spec['air']['tables'])==11
    n=len(spec['air']['tables'])
    if wire[:8]!=codec.magic('affine-v1') or len(wire)<8+48*n:raise ValueError('nibble envelope framing')
    roots=[wire[8+48*i:8+48*(i+1)].hex() for i in range(n)]
    codec.decode(wire,spec,roots,queries=queries,terminal_profile='affine-v1')
    return roots[-1]


def main():
    p=argparse.ArgumentParser();p.add_argument('--capture',type=Path);p.add_argument('--queries',type=int,required=True)
    p.add_argument('--verify',type=Path);p.add_argument('--spec',type=Path);a=p.parse_args()
    if a.verify:
        assert a.spec and not a.capture
        print('PASS compression relation; boundary root '+verify(a.verify.read_bytes(),read(a.spec),a.queries));return
    assert a.capture and not a.spec
    out=a.capture.resolve();report=read(out/'prover-report.json');prepared=read(out/'preparation.json');statement=read(out/'statement.json')
    assert report['status']=='PASS' and report['weighted_pcs']['verified'] and report['weighted_pcs']['queries']==a.queries
    assert report['terminal_profile']=='affine-v1' and report['commitment_profile']=='separate'
    assert report['source_sha256']==[prepared['files'][f'source/source-{i:02d}-rows.json'] for i in range(11)]
    reduction=read(out/'proof/reduction.json');opening=(out/'proof/proof.bin').read_bytes()
    started=time.monotonic();wire=codec.encode(reduction,opening,statement['spec'],statement['roots'],queries=a.queries,terminal_profile='affine-v1')
    (out/'compression.bin').write_bytes(wire)
    specraw=json.dumps(statement['spec'],sort_keys=True,separators=(',',':')).encode()
    specpath=out/'trusted-spec.json.gz';specpath.write_bytes(gzip.compress(specraw,mtime=0))
    encode_seconds=time.monotonic()-started
    started=time.monotonic();fresh=subprocess.run([sys.executable,str(Path(__file__).resolve()),'--verify',str(out/'compression.bin'),'--spec',str(specpath),'--queries',str(a.queries)],capture_output=True,text=True)
    (out/'fresh-envelope.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode();verify_seconds=time.monotonic()-started
    assert fresh.stdout.strip()=='PASS compression relation; boundary root '+prepared['boundary_root']
    badcases=[]
    for name,bad in [('wrong-version',b'X'+wire[1:]),('truncated',wire[:-1]),('trailing',wire+b'\0'),('altered-source-root',wire[:8]+bytes([wire[8]^1])+wire[9:])]:
        try:verify(bad,statement['spec'],a.queries)
        except (ValueError,AssertionError):badcases.append(name)
        else:raise AssertionError('accepted '+name)
    result=dict(status='DIAGNOSTIC_64_BLOCK_COMPRESSION_ENVELOPE_VERIFIED',blocks=prepared['blocks'],queries=a.queries,
        proof_bytes=len(wire),opening_bytes=len(opening),nonopening_bytes=len(wire)-len(opening),
        public_field_elements=0,static_trusted_spec_bytes=len(specraw),boundary_root=prepared['boundary_root'],
        fresh_verifier_passed=True,negative_cases=badcases,encode_and_verify_seconds=encode_seconds,fresh_verify_seconds=verify_seconds,
        proof_sha256=hashlib.sha256(wire).hexdigest(),
        scope='Complete diagnostic compression-relation envelope with all source/aux commitments and local/GKR/PCS messages. Static trusted AIR/spec excluded; roots parsed from wire, no trace or original hash calls required. Boundary root is not linked to application/recursive calls. No zero-knowledge, formal compiler, PQ128, full NEAR or secure-size claim.')
    (out/'codec-report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
