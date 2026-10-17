"""Scripted challenge regressions: zero equality weight cannot authenticate data.
No claim about frequency or Fiat--Shamir challenge manipulation.
"""
import argparse,json,hashlib
from pathlib import Path
import pq384_ext8_reusable_codec as c
from test_pq384_ext8_reusable import independent_claim
p=c.p;e=p.e

def build(coeff,cfg,root,alter_terminal):
    t=p.start(cfg,root);cs=[e.base(x) for x in coeff];ws=p.eqweights(cfg['point'])
    trees=[p.source_tree(coeff,cfg)];rounds=[];claim=e.canonical(cfg['claim']);d=len(cs)
    while d>1:
        q=[list(x) for x in e.quadratic(cs,ws)];r,claim=p.round_start(t,q,claim)
        cs=e.affine_fold(cs,r);ws=e.affine_fold(ws,r);d//=2
        if d==1 and alter_terminal:cs=[e.add(cs[0],e.ONE)]
        tree=p.tree(cs,p.fold_context(t.seed,d),False);trees.append(tree)
        rounds.append(dict(quadratic=q,root=tree['root'].hex()));t.commit(b'ext8/next-root',tree['root'])
    assert ws[0]==e.ZERO and claim==e.ZERO
    assert e.mul(cs[0],ws[0])==claim
    terminal=list(cs[0]);t.commit(b'ext8/terminal',p.extbytes(terminal))
    queries=[]
    for s in p.sample(t,4*cfg['degree'],cfg['queries']):
        d=cfg['degree'];chain=[]
        for j in range(len(rounds)):
            chain.append([p.opening(trees[j],s%(2*d)),p.opening(trees[j+1],s%d)]);d//=2
        queries.append(chain)
    return dict(profile=p.PROFILE,rounds=rounds,terminal=terminal,queries=queries)

def run():
    original=p.h.Transcript;reports=[]
    for first,point0 in [(e.ZERO,e.ONE),(e.ONE,e.ZERO)]:
        schedule=[first,e.ONE,e.ZERO]
        class Scripted(original):
            def __init__(self,statement):super().__init__(statement);self.fold_index=0
            def draw(self,label,count,coefficients,max_blocks=4096):
                values,meta=super().draw(label,count,coefficients,max_blocks)
                if label==b'ext8/fold':
                    assert count==1 and coefficients==8
                    value=schedule[self.fold_index];self.fold_index+=1
                    self.commit(b'test-only-scripted-fold',p.extbytes(value));return [list(value)],meta
                return values,meta
        p.h.Transcript=Scripted
        try:
            coeff=[77+12345*i+17*i*i for i in range(8)]
            point=[list(point0),[3,5,7,11,13,17,19,23],list(e.ONE)]
            cfg=dict(profile=p.PROFILE,degree=8,queries=314,point=point,claim=list(independent_claim(coeff,point)),statement=b'zero-weight-test'.hex(),source_namespace=b'zero-weight-source'.hex())
            root=p.source_tree(coeff,cfg)['root'];honest=build(coeff,cfg,root,False)
            assert p.verify(honest,cfg,root);wire=c.encode(honest,cfg,root)
            assert c.decode(wire,cfg,root)==honest and c.verify(wire,cfg,root)
            bad=build(coeff,cfg,root,True)
            # Recomputed root, terminal authentication, residual and transcript
            # pass. All paths below are fresh and valid under the altered roots.
            roots,contexts,samples,_=c.metadata(bad,cfg,root)
            for s,chain in zip(samples,bad['queries']):
                d=8
                for j,pair in enumerate(chain):
                    p.read_opening(pair[0],roots[j],contexts[j],d,s%(2*d),j==0)
                    p.read_opening(pair[1],roots[j+1],contexts[j+1],d//2,s%d,False);d//=2
            try:p.verify(bad,cfg,root)
            except ValueError as ex:assert str(ex)=='fold consistency'
            else:raise AssertionError('zero-weight altered terminal accepted')
            reports.append(dict(first_fold=list(first),first_point=list(point0),honest_verified=True,codec_roundtrip=True,zero_terminal_residual=True,altered_terminal_root_authenticated=True,all_altered_paths_authenticated=True,rejected_by='fold consistency',queries=314))
        finally:p.h.Transcript=original
    return dict(status='PASS',cases=reports,scope='Scripted zero/one fold challenges; adversarial terminal is freshly committed and paths regenerated. No hash-uniformity or QROM claim.')
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();r=run();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
