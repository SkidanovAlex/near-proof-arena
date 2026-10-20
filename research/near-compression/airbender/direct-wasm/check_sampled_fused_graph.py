"""Prove linked hashes AND one-block challenge sampling for the fused GKR fixture."""
import argparse,gzip,json,os,re,subprocess
from fractions import Fraction
from pathlib import Path
from check_binius_hash_graph import ROOT,PIN,export
OUT=ROOT/'results/swirl-security-review/sampled-fused-graph'
BASE=OUT.parent/'fused-gkr-candidate'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--reuse-tmp',action='store_true')
    args=ap.parse_args();repo=Path('/tmp/nearproof-binius64');OUT.mkdir(exist_ok=True)
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==PIN
    graph=json.loads((BASE/'graph.json').read_text());sliced,counts=export(graph,437)
    assert sliced['nodes']==graph['nodes'] and sliced['inputs']==graph['inputs']
    for draw in graph['draws']:
        assert draw['blocks']==1
        digest=bytes.fromhex(graph['nodes'][draw['scans'][0]['hash_node']]['digest'])
        values=[int.from_bytes(digest[i:i+4],'little') for i in range(0,48,4)]
        expected=[w%2013265921 for w in values if w<4026531842][:4]
        assert expected==draw['values'] and len(expected)==4
    input_words=sum((len(bytes.fromhex(v))+7)//8 for v in graph['inputs'].values())
    counts['public_inout_words']=input_words+4*len(graph['draws'])+6
    counts['public_inout_bytes']=8*counts['public_inout_words']
    env=os.environ.copy();env['RAYON_NUM_THREADS']='4'
    for name in ['NEARPROOF_PARAMETER_SCREEN','NEARPROOF_SIZE_CENSUS','NEARPROOF_GRAPH_BAD_INPUT']:env.pop(name,None)
    exe=str(repo/'target/release/binius-examples');path=str(BASE/'graph.json')
    def run(label,command,bad=False,screen=False):
        e=env.copy()
        if bad:e['NEARPROOF_GRAPH_BAD_INPUT']='1'
        if screen:e['NEARPROOF_PARAMETER_SCREEN']='1'
        p=subprocess.run([exe,'nearproof_hash_graph','--graph',path,'--sample-challenges',*command,'--graph',path,'--sample-challenges','--log-inv-rate','3'],cwd=repo,env=e,capture_output=True,text=True)
        log=p.stdout+p.stderr;(OUT/(label+'.log.gz')).write_bytes(gzip.compress(log.encode(),mtime=0))
        return p.returncode,re.sub(r'\x1b\[[0-9;]*m','',log)
    proof=OUT/'proof.bin'
    if args.reuse_tmp:
        proof.write_bytes(Path('/tmp/nearproof-sampled-graph.proof').read_bytes())
        log=Path('/tmp/nearproof-sampled-graph.log').read_text()
        (OUT/'prove.log.gz').write_bytes(gzip.compress(log.encode(),mtime=0));log=re.sub(r'\x1b\[[0-9;]*m','',log)
    else:
        code,log=run('prove',['prove','--output',str(proof)],screen=True);assert code==0,log[-1500:]
    assert 'Proof written to' in log and 'Verify PCS Opening' in log
    payload=int(re.search(r'proof_size_bytes[^0-9]+([0-9]+)',log)[1]);assert payload+36==proof.stat().st_size
    rows=[]
    for bits,rate,q,a,m,l,total in re.findall(r'NEARPROOF_SCREEN query_bits=(\d+) rate_log=(\d+) queries=(\d+) algebra=(\d+) merkle=(\d+) leaves=(\d+) total=(\d+)',log):
        bits,rate,q,a,m,l,total=map(int,(bits,rate,q,a,m,l,total));err=Fraction((1<<rate)+1,1<<(rate+1))
        assert err**q<=Fraction(1,1<<bits)<err**(q-1) and a+m+l==total
        rows.append(dict(query_bits=bits,rate_log=rate,queries=q,algebra_bytes=a,merkle_bytes=m,leaf_bytes=l,serialized_bytes=total+36))
    assert len(rows)==30
    assert next(r for r in rows if r['query_bits']==96 and r['rate_log']==3)['serialized_bytes']==proof.stat().st_size
    for label,bad in [('fresh',False),('bad-input',True)]:
        code,log=run(label,['verify',str(proof)],bad=bad)
        assert code==(1 if bad else 0),log[-1500:]
        assert ('invalid assertion: value is not zero' if bad else 'Proof verified successfully') in log
    altered=bytearray(proof.read_bytes());altered[len(altered)//2]^=1
    path2=OUT/'altered-proof.bin';path2.write_bytes(altered)
    code,log=run('bad-proof',['verify',str(path2)]);assert code==1 and 'Merkle tree error' in log,log[-1500:]
    best=[min((r for r in rows if r['query_bits']==b),key=lambda r:r['serialized_bytes']) for b in [96,128,160,256,272]]
    report=dict(upstream_commit=PIN,**counts,serialized_bytes=proof.stat().st_size,query_screen=rows,best_per_budget=best,
        checks=['fresh verification','changed public input rejects','changed proof rejects','30 exact query checks','native census matches generated payload'],
        scope='Fixed linked hash graph plus constrained single-block sample for all 437 challenges; no GKR arithmetic or native PCS continuation.',
        limitations=['No QROM security theorem, PQ128, full NEAR or Lean refinement.',
                    'Only96-bit query-budget rate1/8 proof generated; stronger-budget rows are cost estimates.',
                    'Unchanged field/digest widths; public inputs/outputs external, key transport excluded.', 'No multi-block retry circuit or Rust-to-Lean refinement theorem; fewer than four accepted words rejects.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(counts=counts,bytes=proof.stat().st_size,best=best),indent=2))

if __name__=='__main__':main()
