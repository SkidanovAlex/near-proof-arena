"""Fused Ext4 multiplication probe, not a complete GKR verifier."""
import argparse,gzip,json,os,re,subprocess
from pathlib import Path
from check_binius_hash_graph import ROOT,PIN
OUT=ROOT/'results/swirl-security-review/binius-ext4'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--reuse-tmp',action='store_true');args=ap.parse_args()
    repo=Path('/tmp/nearproof-binius64');OUT.mkdir(exist_ok=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    env=os.environ.copy();env['RAYON_NUM_THREADS']='4'
    for name in ['NEARPROOF_EXT4_BAD_INPUT','NEARPROOF_PARAMETER_SCREEN','NEARPROOF_SIZE_CENSUS']:env.pop(name,None)
    def run(label,command,bad=False,census=False):
        e=env.copy()
        if bad:e['NEARPROOF_EXT4_BAD_INPUT']='1'
        if census:e['NEARPROOF_SIZE_CENSUS']='1'
        p=subprocess.run([str(repo/'target/release/binius-examples'),'nearproof_ext4',*command],cwd=repo,env=e,capture_output=True,text=True)
        log=p.stdout+p.stderr;(OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(),mtime=0))
        return p.returncode,re.sub(r'\x1b\[[0-9;]*m','',log)
    proof=OUT/'proof.bin'
    if args.reuse_tmp:
        proof.write_bytes(Path('/tmp/nearproof-ext4.proof').read_bytes())
        (OUT/'prove.log.gz').write_bytes(gzip.compress(Path('/tmp/nearproof-ext4-prove.log').read_bytes(),mtime=0))
    else:
        code,log=run('prove',['prove','--count','16','--log-inv-rate','3','--output',str(proof)]);assert code==0,log[-1200:]
    code,log=run('fresh',['verify',str(proof),'--count','16','--log-inv-rate','3'],census=True)
    assert code==0 and 'Proof verified successfully' in log,log[-1200:]
    r,q,a,m,l,total=map(int,re.search(r'NEARPROOF_CENSUS rate_log=(\d+) queries=(\d+) algebra=(\d+) merkle=(\d+) leaves=(\d+) total=(\d+)',log).groups())
    assert a+m+l==total and total+36==proof.stat().st_size
    code,log=run('bad-input',['verify',str(proof),'--count','16','--log-inv-rate','3'],bad=True)
    assert code==1 and 'invalid assertion: value is not zero' in log,log[-1500:]
    altered=bytearray(proof.read_bytes());altered[len(altered)//2]^=1
    path=OUT/'altered-proof.bin';path.write_bytes(altered)
    code,log=run('bad-proof',['verify',str(path),'--count','16','--log-inv-rate','3'])
    assert code==1 and 'Merkle tree error' in log,log[-1500:]
    for n in [1,16]:
        code,log=run(f'stat-{n}',['stat','--count',str(n)]);assert code==0
        for text in [f'Private Section: {120*n:,}',f'AND constraints: {64*n:,}',f'ZERO constraints: {72*n:,}',f'IMUL constraints: {26*n:,}']:assert text in log,text
    testenv=env.copy();testenv['RUSTFLAGS']='-C target-cpu=native';testenv['CARGO_BUILD_JOBS']='4'
    test=subprocess.run(['cargo','test','--locked','--release','-p','binius-examples','--lib','nearproof_ext4','--','--nocapture'],cwd=repo,env=testenv,capture_output=True,text=True)
    testlog=test.stdout+test.stderr;(OUT/'tests.log.gz').write_bytes(gzip.compress(testlog.encode(),mtime=0))
    assert test.returncode==0 and '2 passed; 0 failed' in testlog,testlog[-1500:]
    assert 'Private Section: 255' in testlog and 'IMUL constraints: 44' in testlog
    report=dict(upstream_commit=PIN,products=16,private_words=1920,public_io_words=192,
        serialized_bytes=proof.stat().st_size,payload_bytes=total,public_io_bytes=1536,
        census=dict(algebra=a,merkle=m,leaf_values=l),scalar_composed_reference=dict(private_words=255,and_constraints=111,zero_constraints=157,imul_constraints=44,bmul_constraints=12),per_product=dict(private_words=120,and_constraints=64,zero_constraints=72,imul_constraints=26),
        checks=['fresh proof verification','changed canonical public input rejected in verifier','changed proof rejected at Merkle authentication','1 and16 product statistics'],
        limitations=['Diagnostic96-bit query budget/rate1/8; not PQ128 or full security audit.',
          'Ext4 multiplication only; no combined GKR verifier.',
          'Standalone public operands/results; integration can change sharing and private/public layout.',
          'Lean wide-addition/remainder soundness is conditional on word-operation equations; no Rust frontend refinement.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
