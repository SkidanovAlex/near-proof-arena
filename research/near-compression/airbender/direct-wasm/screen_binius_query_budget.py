"""Conditional query-budget screen, not a full security certificate.

Uses the pinned native size counter (validated against three actual proofs),
with unchanged graph, field and digest width. Higher query budgets do NOT
upgrade those other components. No QROM theorem is inferred from the numbers.
"""
import argparse,gzip,json,os,re,subprocess
from fractions import Fraction
from pathlib import Path
from check_binius_hash_graph import ROOT,PIN
OUT=ROOT/'results/swirl-security-review/binius-query-screen'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,default=Path('/tmp/nearproof-binius64'))
    args=ap.parse_args();repo=args.repo.resolve();OUT.mkdir(exist_ok=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    env=os.environ.copy();env['RAYON_NUM_THREADS']='4';env['NEARPROOF_PARAMETER_SCREEN']='1'
    env.pop('NEARPROOF_SIZE_CENSUS',None);env.pop('NEARPROOF_GRAPH_BAD_INPUT',None)
    base=OUT.parent;graph=str(base/'binius-hash-graph/graph-437.json')
    p=subprocess.run([str(repo/'target/release/binius-examples'),'nearproof_hash_graph','--graph',graph,
        'verify',str(base/'binius-rate-sweep/rate-3.bin'),'--graph',graph,'--log-inv-rate','3'],
        cwd=repo,env=env,capture_output=True,text=True)
    log=p.stdout+p.stderr;(OUT/'screen.log.gz').write_bytes(gzip.compress(log.encode(),mtime=0))
    assert p.returncode==0 and 'Proof verified successfully' in log,log[-2000:]
    found=re.findall(r'NEARPROOF_SCREEN query_bits=(\d+) rate_log=(\d+) queries=(\d+) algebra=(\d+) merkle=(\d+) leaves=(\d+) total=(\d+)',log)
    rows=[];seen=set()
    for entry in found:
        bits,rate,q,a,m,l,total=map(int,entry);assert (bits,rate) not in seen;seen.add((bits,rate))
        err=Fraction((1<<rate)+1,1<<(rate+1));budget=Fraction(1,1<<bits)
        assert err**q<=budget and err**(q-1)>budget
        assert a+m+l==total
        rows.append(dict(query_bits=bits,log_inverse_rate=rate,queries=q,algebra_bytes=a,
            merkle_bytes=m,leaf_bytes=l,payload_bytes=total,serialized_bytes=total+36,
            with_public_io_bytes=total+36+45200))
    assert seen=={(b,r) for b in (96,128,160,256,272) for r in range(1,7)}
    measured=json.loads((base/'binius-rate-sweep/report.json').read_text())['rows']
    for prior in measured:
        row=next(x for x in rows if x['query_bits']==96 and x['log_inverse_rate']==prior['log_inverse_rate'])
        for key,value in prior.items():assert row[key]==value,(key,row,prior)
    best=[min((x for x in rows if x['query_bits']==b),key=lambda x:x['serialized_bytes']) for b in (96,128,160,256,272)]
    report=dict(upstream_commit=PIN,rows=rows,best_per_query_budget=best,
        checks=['30 exact rational query sufficiency and minimality checks',
                'matches all byte categories for three measured proofs','original rate3 proof still verifies'],
        scope='Fixed GKR hash graph only; code rates up to 1/64; estimates for stronger query settings, not generated proofs.',
        limitations=['Query-only budgets 96/128/160/256/272 are sensitivity points, not claimed quantum security levels.',
          'Unchanged 128-bit binary field and 32-byte SHA256 Merkle digests; no enlarged-field/hash costs.',
          'No folding, algebraic, hash, Fiat-Shamir or recursive composition error budget established.',
          'No arbitrary sampler, GKR arithmetic, prefix/PCS verifier, full NEAR, or Lean refinement.',
          'Fixed public input/output count 45200B; graph/verifier-key transport excluded.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(best,indent=2))

if __name__=='__main__':main()
