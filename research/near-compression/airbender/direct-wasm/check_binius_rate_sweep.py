"""Measure unchanged fixed graph at code rates 1/2, 1/4, 1/8.

Requires prior hash-graph, wide-address and census patches on the pinned Binius
checkout. No security parameter upgrade is claimed. Default generates new proofs;
--reuse-tmp imports prior successful runs, then independently verifies each.
"""
import argparse,gzip,json,os,re,subprocess
from pathlib import Path
from check_binius_hash_graph import ROOT,PIN

OUT=ROOT/'results/swirl-security-review/binius-rate-sweep'
BASE=OUT.parent/'binius-hash-graph'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reuse-tmp',action='store_true')
    ap.add_argument('--repo',type=Path,default=Path('/tmp/nearproof-binius64'))
    args=ap.parse_args();repo=args.repo.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    OUT.mkdir(exist_ok=True)
    env=os.environ.copy();env['RAYON_NUM_THREADS']='4';env['NEARPROOF_SIZE_CENSUS']='1'
    env.pop('NEARPROOF_GRAPH_BAD_INPUT',None)
    graph=str(BASE/'graph-437.json');exe=str(repo/'target/release/binius-examples')
    def run(label,rate,command,bad=False):
        e=env.copy()
        if bad:e['NEARPROOF_GRAPH_BAD_INPUT']='1'
        p=subprocess.run([exe,'nearproof_hash_graph','--graph',graph,*command,'--graph',graph,'--log-inv-rate',str(rate)],cwd=repo,env=e,capture_output=True,text=True)
        log=p.stdout+p.stderr
        (OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(),mtime=0))
        return p.returncode,re.sub(r'\x1b\[[0-9;]*m','',log)
    rows=[]
    for rate in [1,2,3]:
        proof=OUT/f'rate-{rate}.bin'
        if args.reuse_tmp:
            prefix='/tmp/nearproof-binius-wide-437' if rate==1 else f'/tmp/nearproof-binius-rate{rate}'
            proof.write_bytes(Path(prefix+'.proof').read_bytes())
            (OUT/f'prove-{rate}.log.gz').write_bytes(gzip.compress(Path(prefix+'.log').read_bytes(),mtime=0))
        else:
            code,log=run(f'prove-{rate}',rate,['prove','--output',str(proof)])
            assert code==0,log[-1500:]
        code,log=run(f'fresh-{rate}',rate,['verify',str(proof)])
        assert code==0 and 'Proof verified successfully' in log,log[-1500:]
        matches=re.findall(r'NEARPROOF_CENSUS rate_log=(\d+) queries=(\d+) algebra=(\d+) merkle=(\d+) leaves=(\d+) total=(\d+)',log)
        assert matches
        r,q,a,m,l,total=map(int,matches[-1]);assert r==rate and a+m+l==total
        assert total+36==proof.stat().st_size,(total,proof.stat().st_size)
        rows.append(dict(log_inverse_rate=r,queries=q,algebra_bytes=a,merkle_bytes=m,leaf_bytes=l,payload_bytes=total,serialized_bytes=proof.stat().st_size,with_public_io_bytes=proof.stat().st_size+45200))
    code,log=run('bad-input',3,['verify',str(OUT/'rate-3.bin')],True)
    assert code==1 and 'invalid assertion: value is not zero' in log,log[-1500:]
    data=bytearray((OUT/'rate-3.bin').read_bytes());data[len(data)//2]^=1
    altered=OUT/'altered-proof.bin';altered.write_bytes(data)
    code,log=run('bad-proof',3,['verify',str(altered)])
    assert code==1 and 'Merkle tree error' in log,log[-1500:]
    report=dict(upstream_commit=PIN,rows=rows,public_io_bytes=45200,
        scope='Same fixed 2187-hash graph; no field sampler, GKR arithmetic, prefix/PCS verifier, full NEAR or Lean refinement.',
        security='Unchanged SECURITY_BITS=96 controls FRI query phase only; default SHA256, not PQ128.',
        census='Upstream SizeTrackingChannel executed with counters. Exact total matched all three serialized payloads; not a soundness proof.',
        checks=['three fresh verifications','rate3 changed input rejected','rate3 changed proof rejected'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
