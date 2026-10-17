#!/usr/bin/env python3
import argparse,copy,json,subprocess,sys,time,hashlib
from pathlib import Path
import pq384_ext8_codec as c
p=c.p;e=p.e

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--verify-only',action='store_true');args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    if args.verify_only:
        cfg=json.loads((args.output/'config.json').read_text());root=bytes.fromhex((args.output/'root.txt').read_text());assert c.verify((args.output/'proof.bin').read_bytes(),cfg,root);print('PASS fresh binary verifier');return
    reports=[]
    for d in (32,1024):
        directory=args.output/str(d);directory.mkdir(exist_ok=True)
        coeff=[(i*i*9876543+i*12345+77)%e.P for i in range(d)]
        point=[[(i+1)*(j+2)*137%e.P for j in range(8)] for i in range(d.bit_length()-1)];claim=e.ZERO
        for v,w in zip(coeff,p.eqweights(point)):claim=e.add(claim,e.scale(w,v))
        cfg=dict(profile=p.PROFILE,degree=d,queries=314,point=point,claim=list(claim),statement=b'Ext8 multiproof same314queries'.hex())
        root=p.source_tree(coeff,cfg)['root'];t=time.perf_counter();proof=p.prove(coeff,cfg,root);prove_secs=time.perf_counter()-t
        t=time.perf_counter();wire=c.encode(proof,cfg,root);encoded_secs=time.perf_counter()-t
        t=time.perf_counter();decoded=c.decode(wire,cfg,root);assert decoded==proof;assert p.verify(decoded,cfg,root);verify_secs=time.perf_counter()-t
        rejected=[]
        def reject(name,b,cfg1=cfg,root1=root):
            try:c.verify(b,cfg1,root1)
            except (ValueError,TypeError,KeyError,IndexError):rejected.append(name)
            else:raise AssertionError(name)
        for i in (0,8,56,88,152,len(wire)//2,len(wire)-1):
            b=bytearray(wire);b[i]^=1;reject('byte'+str(i),bytes(b))
        for n in (0,8,55,56,len(wire)//2,len(wire)-1):reject('truncate'+str(n),wire[:n])
        reject('trailing',wire+b'\0');reject('wrong expectedroot',wire,cfg,bytes(48))
        reject('wrong config',wire,{**cfg,'queries':313});reject('wrong statement',wire,{**cfg,'statement':'00'})
        reject('noncanonical coordinate',wire[:56]+e.P.to_bytes(4,'little')+wire[60:])
        (directory/'proof.bin').write_bytes(wire);(directory/'config.json').write_text(json.dumps(cfg));(directory/'root.txt').write_text(root.hex())
        child=subprocess.run([sys.executable,__file__,'--output',str(directory),'--verify-only'],check=True,capture_output=True,text=True)
        b=c.breakdown(proof,cfg,root);assert len(wire)==b['total_bytes']
        reports.append(dict(degree=d,queries=314,binary_bytes=len(wire),complete_with_external_config_bytes=len(wire)+len(p.config_bytes(cfg)),
          expanded_json_bytes=len(json.dumps(proof,separators=(',',':')).encode()),prove_seconds=prove_secs,encode_seconds=encoded_secs,decode_verify_seconds=verify_secs,
          exact_roundtrip=True,negative_count=len(rejected),negatives=rejected,fresh_process=child.stdout.strip(),breakdown=b,
          proof_sha256=hashlib.sha256(wire).hexdigest()))
    report=dict(status='PASS',cases=reports,scope='Lossless transport only; all314 with-replacement queries retained. Tiny-source saturation must not be extrapolated.',
       sources=[dict(path=str(x),sha256=hashlib.sha256(x.read_bytes()).hexdigest()) for x in [Path(__file__),Path(c.__file__)]])
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
