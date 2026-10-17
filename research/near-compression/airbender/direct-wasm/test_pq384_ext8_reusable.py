#!/usr/bin/env python3
import argparse,copy,json,hashlib,subprocess,sys,time
from pathlib import Path
import pq384_ext8_reusable_codec as c
p=c.p;e=p.e

def independent_claim(coeff,point):
    out=e.ZERO
    for i,value in enumerate(coeff):
        term=e.base(value)
        for j,u in enumerate(point):term=e.mul(term,tuple(u) if (i>>j)&1 else e.sub(e.ONE,tuple(u)))
        out=e.add(out,term)
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--verify-only',action='store_true');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    if a.verify_only:
        cfg=json.loads((a.output/'config.json').read_text());root=bytes.fromhex((a.output/'root.txt').read_text());assert c.verify((a.output/'proof.bin').read_bytes(),cfg,root);print('PASS fresh reusable binary');return
    cases=[]
    for d in (32,1024):
        coeff=[(i*i*9876543+i*12345+77)%e.P for i in range(d)];roots=[];configs=[];wires=[];measure=[]
        for which in (0,1):
            point=[[(i+1)*(j+2)*137+which*(j*j+17*i+43) for j in range(8)] for i in range(d.bit_length()-1)]
            claim=independent_claim(coeff,point)
            cfg=dict(profile=p.PROFILE,degree=d,queries=314,point=point,claim=list(claim),statement=('opening-'+str(which)).encode().hex(),source_namespace=b'fixed-source-fixture/v2/layout-1'.hex())
            tree=p.source_tree(coeff,cfg);root=tree['root'];roots.append(root);configs.append(cfg)
            t=time.perf_counter();proof=p.prove(coeff,cfg,root);wire=c.encode(proof,cfg,root);assert c.decode(wire,cfg,root)==proof;assert c.verify(wire,cfg,root);elapsed=time.perf_counter()-t
            wires.append(wire);out=a.output/str(d)/str(which);out.mkdir(parents=True,exist_ok=True)
            (out/'proof.bin').write_bytes(wire);(out/'config.json').write_text(json.dumps(cfg));(out/'root.txt').write_text(root.hex())
            fresh=subprocess.run([sys.executable,__file__,'--output',str(out),'--verify-only'],check=True,capture_output=True,text=True)
            measure.append(dict(point_index=which,bytes=len(wire),bytes_with_external_config=len(wire)+len(p.config_bytes(cfg)),prove_codec_verify_seconds=elapsed,fresh_process=fresh.stdout.strip(),sha256=hashlib.sha256(wire).hexdigest()))
        assert roots[0]==roots[1];assert configs[0]['claim']!=configs[1]['claim'];assert wires[0]!=wires[1]
        rejected=[]
        def reject(name,wire,cfg,root):
            try:c.verify(wire,cfg,root)
            except (ValueError,TypeError,KeyError,IndexError):rejected.append(name)
            else:raise AssertionError(name)
        for i in (0,1):
            cfg=configs[i];wire=wires[i];root=roots[i]
            reject('cross-opening'+str(i),wire,configs[1-i],root)
            for key,value in [('point',configs[1-i]['point']),('claim',configs[1-i]['claim']),('statement','00'),('source_namespace','01'),('queries',313),('profile','near-pq384-ext8-scalar-equality-fold-v1')]:
                reject(str(i)+key,wire,{**cfg,key:value},root)
            reject('root'+str(i),wire,cfg,bytes(48));reject('old-magic'+str(i),b'NP8MP001'+wire[8:],cfg,root)
            reject('trailing'+str(i),wire+b'\0',cfg,root);reject('truncated'+str(i),wire[:-1],cfg,root)
        # Source root invariance covers every opening-only field, but not namespace.
        varied={**configs[0],'point':configs[1]['point'],'claim':configs[1]['claim'],'queries':1,'statement':'deadbeef'}
        assert p.source_tree(coeff,varied)['root']==roots[0]
        assert p.source_tree(coeff,{**varied,'source_namespace':'01'})['root']!=roots[0]
        bad=coeff[:];bad[0]=(bad[0]+1)%e.P
        try:p.prove(bad,configs[0],roots[0])
        except ValueError:rejected.append('fresh source alteration')
        else:raise AssertionError('source mutation')
        cases.append(dict(degree=d,queries=314,shared_root=roots[0].hex(),same_root_for_two_points=True,independent_claims=True,openings=measure,negative_count=len(rejected),negatives=rejected))
    report=dict(status='PASS',cases=cases,scope='Reusable scalar source context, not packed/joint AIR yet. Query count314 unchanged. Ideal replay term only; root extraction/FS/QROM/upstream composition open.',
        files=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in [Path(__file__),Path(c.__file__),Path(p.__file__)]])
    (a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
