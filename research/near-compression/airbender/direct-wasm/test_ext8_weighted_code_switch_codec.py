"""Compact transport parity, fresh verification and malformed-byte tests."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from pathlib import Path
import ext8_weighted_code_switch_codec as c
from pq384_ext8_native import Kernel
from test_ext8_input_weights import coefficient_claim
f=c.a.f


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);x=p.parse_args();x.output.mkdir(parents=True,exist_ok=True)
    retained=Path('results/ext8-weighted-code-switch');s=json.loads((retained/'statement.json').read_text());proof=json.loads((retained/'proof.json').read_text())
    def params(s):return bytes.fromhex(s['statement']),bytes.fromhex(s['parent']),s['branches'],s['claim'],s['config']
    args=params(s);wire=c.encode(proof,*args);assert c.decode(wire,*args)==proof and c.encode(c.decode(wire,*args),*args)==wire
    detail=c.breakdown(wire,*args);assert detail['total_bytes']==len(wire)
    (x.output/'proof.bin').write_bytes(wire);(x.output/'statement.json').write_bytes(c.a.stage.canonical_json(s))
    fresh=subprocess.run([sys.executable,c.__file__,'--proof',str(x.output/'proof.bin'),'--statement',str(x.output/'statement.json')],text=True,capture_output=True);(x.output/'fresh-verifier.log').write_text(fresh.stdout+fresh.stderr);fresh.check_returncode()
    negative=[]
    def reject(name,bad,st=s):
        try:c.decode(bad,*params(st))
        except ValueError:negative.append(name)
        else:raise AssertionError(name)
    reject('truncated',wire[:-1]);reject('trailing',wire+b'\0');reject('version',b'BADMAGIC'+wire[8:]);reject('noncanonical',wire[:8]+f.P.to_bytes(4,'little')+wire[12:])
    for name,pos in [('input-quadratic',8),('first-quadratic',8+96*6),('first-root',8+96*7),('ood-answer',8+96*7+48),('terminal',len(wire)-32)]:
        reject(name,wire[:pos]+bytes([wire[pos]^1])+wire[pos+1:])
    for i,g in enumerate(detail['groups']):
        at=g['offset'];reject('group-value-'+str(i),wire[:at]+bytes([wire[at]^1])+wire[at+1:])
        at+=g['leaf_bytes']
        if g['sibling_bytes']:reject('group-auth-'+str(i),wire[:at]+bytes([wire[at]^1])+wire[at+1:])
        reject('truncated-group-'+str(i),wire[:g['offset']])
    st=copy.deepcopy(s);st['config']['tail_steps'][0]['queries']-=1;reject('external-schedule',wire,st)
    st=copy.deepcopy(s);st['branches'][0]['root']='ab'*48;reject('external-root',wire,st)
    st=copy.deepcopy(s);st['claim']=list(f.add(st['claim'],f.ONE));reject('external-claim',wire,st)
    # Same root/context/indices with distinct logical weights shares bytes but
    # both logical branches remain in the verified functional.
    rng=random.Random(942071);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8))
    with tempfile.TemporaryDirectory(prefix='switch-codec-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(Path(__file__).with_name('native-folded')/'kernel_ext8.rs'),'-o',str(lib)],check=True);native=Kernel(lib)
        assert c.encode(proof,*args,native=native)==wire and c.decode(wire,*args,native=native)==proof
        rows=[[rng.randrange(f.P) for _ in range(3)] for _ in range(8)];cache=c.a.pcs.Source(rows,2,native);branches=[];claim=f.ZERO
        for _ in range(2):
            b=dict(root=cache.root.hex(),log_rows=3,width=3,packing=2,row_point=[scalar() for _ in range(3)],lanes=[[[scalar() if 2*j+k<3 else f.ZERO for k in range(2)] for _ in range(2)] for j in range(2)])
            branches.append(b);claim=f.add(claim,coefficient_claim(rows,b))
        config=dict(queries=31,child_blowup=8,child_fold_bits=2,tail_steps=[dict(next_blowup=8,next_fold_bits=0,queries=31)])
        shared=c.a.prove([cache,cache],native,b'shared',b'parent',branches,claim,config);args2=(b'shared',b'parent',branches,claim,config)
        shared_wire=c.encode(shared,*args2,native=native);assert c.decode(shared_wire,*args2)==shared
        shared_detail=c.breakdown(shared_wire,*args2);assert sum(g['shared'] for g in shared_detail['groups'])==1
        # Verify that old per-query paths survived compression exactly, including duplicates.
        assert c.decode(shared_wire,*args2)['first']['source_openings']==shared['first']['source_openings']
    report=dict(status='PASS',binary_bytes=len(wire),retained_json_bytes=(retained/'proof.json').stat().st_size,roundtrip_exact=True,sha256=hashlib.sha256(wire).hexdigest(),breakdown=detail,shared_source=dict(binary_bytes=len(shared_wire),breakdown=shared_detail),native_reference_identical=True,negative_cases=negative,fresh_verifier=fresh.stdout.strip(),scope='Small experimental packed-root code-switch proof transport; no full execution envelope, source extraction/proximity/QROM or PQ128 certificate. Decoding checks the continuing obligation, not only authentication.')
    (x.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
