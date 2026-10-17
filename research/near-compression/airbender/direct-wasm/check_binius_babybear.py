"""Canonical modular multiplication probe, not a complete GKR verifier."""
import argparse,gzip,json,os,re,subprocess
from pathlib import Path
from check_binius_hash_graph import ROOT,PIN
OUT=ROOT/'results/swirl-security-review/binius-babybear'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--reuse-tmp',action='store_true');args=ap.parse_args()
    repo=Path('/tmp/nearproof-binius64');OUT.mkdir(exist_ok=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    env=os.environ.copy();env['RAYON_NUM_THREADS']='4'
    for name in ['NEARPROOF_BABYBEAR_BAD_INPUT','NEARPROOF_PARAMETER_SCREEN','NEARPROOF_SIZE_CENSUS']:env.pop(name,None)
    def run(label,command,bad=False,census=False):
        e=env.copy()
        if bad:e['NEARPROOF_BABYBEAR_BAD_INPUT']='1'
        if census:e['NEARPROOF_SIZE_CENSUS']='1'
        p=subprocess.run([str(repo/'target/release/binius-examples'),'nearproof_babybear',*command],cwd=repo,env=e,capture_output=True,text=True)
        log=p.stdout+p.stderr;(OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(),mtime=0))
        return p.returncode,re.sub(r'\x1b\[[0-9;]*m','',log)
    proof=OUT/'proof.bin'
    if args.reuse_tmp:
        proof.write_bytes(Path('/tmp/nearproof-babybear.proof').read_bytes())
        (OUT/'prove.log.gz').write_bytes(gzip.compress(Path('/tmp/nearproof-babybear-prove.log').read_bytes(),mtime=0))
    else:
        code,log=run('prove',['prove','--count','64','--log-inv-rate','3','--output',str(proof)]);assert code==0,log[-1200:]
    code,log=run('fresh',['verify',str(proof),'--count','64','--log-inv-rate','3'],census=True)
    assert code==0 and 'Proof verified successfully' in log,log[-1200:]
    r,q,a,m,l,total=map(int,re.search(r'NEARPROOF_CENSUS rate_log=(\d+) queries=(\d+) algebra=(\d+) merkle=(\d+) leaves=(\d+) total=(\d+)',log).groups())
    assert a+m+l==total and total+36==proof.stat().st_size
    code,log=run('bad-input',['verify',str(proof),'--count','64','--log-inv-rate','3'],bad=True)
    assert code==1 and 'invalid assertion: value is not zero' in log,log[-1500:]
    altered=bytearray(proof.read_bytes());altered[len(altered)//2]^=1
    path=OUT/'altered-proof.bin';path.write_bytes(altered)
    code,log=run('bad-proof',['verify',str(path),'--count','64','--log-inv-rate','3'])
    assert code==1 and 'Merkle tree error' in log,log[-1500:]
    for n in [1,64]:
        code,log=run(f'stat-{n}',['stat','--count',str(n)]);assert code==0
        for text in [f'Private Section: {10*n}',f'AND constraints: {5*n}',f'ZERO constraints: {8*n}',f'IMUL constraints: {2*n}']:assert text in log,text
    report=dict(upstream_commit=PIN,products=64,private_words=640,public_io_words=192,
        serialized_bytes=proof.stat().st_size,payload_bytes=total,public_io_bytes=1536,
        census=dict(algebra=a,merkle=m,leaf_values=l),per_product=dict(private_words=10,and_constraints=5,zero_constraints=8,imul_constraints=2),
        checks=['fresh proof verification','changed canonical public input rejected in verifier','changed proof rejected at Merkle authentication','1 and64 product statistics'],
        limitations=['Diagnostic96-bit query budget/rate1/8; not PQ128 or full security audit.',
          'Canonical base-field multiplication only; no Ext4 arithmetic or combined GKR verifier.',
          'Standalone public operands/results; integration can change sharing and private/public layout.',
          'Lean natural-number soundness is conditional on word-operation equations; no Rust frontend refinement.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
