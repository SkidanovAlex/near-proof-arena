"""Native proof of dependency-complete GKR equality slice; not full recursion."""
import argparse,gzip,json,os,re,subprocess
from pathlib import Path
from fractions import Fraction
from check_binius_hash_graph import ROOT,PIN
OUT=ROOT/'results/swirl-security-review/fused-gkr-arithmetic'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--reuse-tmp',action='store_true');args=ap.parse_args()
    repo=Path('/tmp/nearproof-binius64');OUT.mkdir(exist_ok=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    env=os.environ.copy();env['RAYON_NUM_THREADS']='4'
    for key in ['NEARPROOF_PARAMETER_SCREEN','NEARPROOF_SIZE_CENSUS','NEARPROOF_GKR_BAD_INPUT']:env.pop(key,None)
    def run(label,command,n=128,bad=False,screen=False):
        e=env.copy()
        if bad:e['NEARPROOF_GKR_BAD_INPUT']='1'
        if screen:e['NEARPROOF_PARAMETER_SCREEN']='1'
        fixture=str(OUT/f'slice-{n}.json')
        p=subprocess.run([str(repo/'target/release/binius-examples'),'nearproof_gkr_slice','--fixture',fixture,*command,'--fixture',fixture],cwd=repo,env=e,capture_output=True,text=True)
        log=p.stdout+p.stderr;(OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(),mtime=0))
        return p.returncode,re.sub(r'\x1b\[[0-9;]*m','',log)
    proof=OUT/'slice-128.proof'
    if args.reuse_tmp:
        proof.write_bytes(Path('/tmp/nearproof-gkr-slice-128.proof').read_bytes());log=Path('/tmp/nearproof-gkr-slice-128.log').read_text()
        (OUT/'native-prove.log.gz').write_bytes(gzip.compress(log.encode(),mtime=0));log=re.sub(r'\x1b\[[0-9;]*m','',log)
    else:
        code,log=run('native-prove',['prove','--log-inv-rate','3','--output',str(proof)],screen=True);assert code==0,log[-1500:]
    assert 'Proof written to' in log and 'Verify PCS Opening' in log
    rows=[]
    for values in re.findall(r'NEARPROOF_SCREEN query_bits=(\d+) rate_log=(\d+) queries=(\d+) algebra=(\d+) merkle=(\d+) leaves=(\d+) total=(\d+)',log):
        bits,rate,q,a,m,l,total=map(int,values);err=Fraction((1<<rate)+1,1<<(rate+1))
        assert err**q<=Fraction(1,1<<bits)<err**(q-1) and a+m+l==total
        rows.append(dict(query_bits=bits,rate_log=rate,queries=q,algebra_bytes=a,merkle_bytes=m,leaf_bytes=l,serialized_bytes=total+36))
    assert len(rows)==30
    assert next(r for r in rows if r['query_bits']==96 and r['rate_log']==3)['serialized_bytes']==proof.stat().st_size
    code,log=run('native-fresh',['verify',str(proof),'--log-inv-rate','3']);assert code==0 and 'Proof verified successfully' in log,log[-1500:]
    code,log=run('bad-input-witness',['verify',str(proof),'--log-inv-rate','3'],bad=True)
    assert code==1 and 'circuit not satisfied' in log,log[-1500:]
    data=bytearray(proof.read_bytes());data[len(data)//2]^=1
    altered=OUT/'altered-proof.bin';altered.write_bytes(data)
    code,log=run('bad-proof',['verify',str(altered),'--log-inv-rate','3']);assert code==1 and 'Merkle tree error' in log,log[-1500:]
    stats=[]
    for n in [32,128]:
        code,log=run(f'native-stat-{n}',['stat'],n);assert code==0
        def count(label):return int(re.search(re.escape(label)+r': ([\d,]+)',log)[1].replace(',',''))
        stats.append(dict(checks=n,private_words=count('Private Section'),public_words=count('Inout'),and_constraints=count('AND constraints'),imul_constraints=count('IMUL constraints'),bmul_constraints=count('BMUL constraints'),zero_constraints=count('ZERO constraints')))
    report=dict(upstream_commit=PIN,serialized_bytes=proof.stat().st_size,public_io_bytes=stats[-1]['public_words']*8,
        stats=stats,query_screen=rows,best_per_budget=[min((r for r in rows if r['query_bits']==b),key=lambda r:r['serialized_bytes']) for b in [96,128,160,256,272]],
        checks=['fresh verification','tampered proof rejected by Merkle verifier','changed challenge rejected EARLIER by witness assertion, not counted as verifier negative'],
        scope='First128GKR equalities only, dependencies included. Inputs are public; no transcript derivation, residual/PCS check, hash circuit or full NEAR.',
        limitations=['Diagnostic96-bit query target, not full security or PQ128.',
          'Stronger query rows are size estimates with unchanged field/hash widths.',
          'No full-DAG byte extrapolation or impossibility theorem.',
          'No Python/Rust/Lean compiler refinement.'])
    (OUT/'native-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(bytes=proof.stat().st_size,stats=stats,best=report['best_per_budget']),indent=2))

if __name__=='__main__':main()
