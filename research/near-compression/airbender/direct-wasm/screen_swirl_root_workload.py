"""Measured trace census and optimistic component-removal sensitivity.

Counterfactual removed AIRs are free, not implementations or sound protocols.
This ranks architecture experiments; it cannot certify feasibility or security.
"""
import hashlib
import json
from pathlib import Path
from screen_swirl_stacking_geometry import cost

ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'results/swirl-security-review'
OUT=BASE/'root-workload-screen'


def main():
    manifest_path=BASE/'root-split-witness/manifest.json'
    chain_path=BASE/'chain/report.json'
    manifest=json.loads(manifest_path.read_text())
    traces=json.loads(chain_path.read_text())['records'][-1]['traces']
    rows=[]
    for m in manifest:
        name=traces[14 if m['air']==39 else m['air']]['air']
        assert m['width']==(12 if m['part']==1 else traces[14 if m['air']==39 else m['air']]['width'])
        rows.append(dict(**m,name=name,cells=m['height']*m['width']))
    common=sum(r['cells'] for r in rows if r['part']==0)
    cached=sum(r['cells'] for r in rows if r['part']==1)
    assert (common,cached)==(9670384,393216)
    def cells(ids):
        return sum(r['cells'] for r in rows if r['part']==0 and r['air'] in ids)
    groups={'hash':cells({14,39}), 'symbolic':cells({0}),
            'initial_openings':cells({32}), 'final_query_eval':cells({36})}
    shapes=[]
    for h in range(15,26):
        for rate in range(2,28-h):
            for fold in range(1,9):
                for terminal in range(1,13):
                    rounds=(h-terminal+fold-1)//fold
                    if h-rounds*fold>=0:shapes.append((h,rate,fold,terminal))
    assert len(shapes)==5790
    scenarios=[('measured',common,False),
        ('half_hash_free',common-(groups['hash']//2),False),
        ('all_hash_free',common-groups['hash'],False),
        ('initial_and_final_eval_free',common-groups['initial_openings']-groups['final_query_eval'],False),
        ('symbolic_and_cache_free',common-groups['symbolic'],True),
        ('hash_symbolic_and_cache_free',common-groups['hash']-groups['symbolic'],True)]
    for divisor in (2,4,8,16):
        for free_cache in (False,True):
            scenarios.append((f'all_common_divided_{divisor}_cache_free_{free_cache}',
                              (common+divisor-1)//divisor,free_cache))
    results=[]
    for name,n,free_cache in scenarios:
        options=[cost(n,cached,h,rate,fold,terminal,9,52,public_cached=free_cache,
                      column_claims=0,constraint_fixed=161+1288,framing_base=296)
                 for h,rate,fold,terminal in shapes]
        best=min(options,key=lambda x:x['expected_frontier_bytes'])
        result=dict(name=name,common_cells=n,free_cache=free_cache,best=best,
                    below_target=sum(x['expected_frontier_bytes']<300000 for x in options))
        results.append(result)
        print(name,round(best['expected_frontier_bytes'],2),result['below_target'])
    paths=[manifest_path,chain_path,Path(__file__),Path(__file__).with_name('screen_swirl_stacking_geometry.py'),
           Path(__file__).with_name('screen_swirl_query_payload.py')]
    OUT.mkdir(exist_ok=True)
    (OUT/'report.json').write_text(json.dumps(dict(common_cells=common,cached_cells=cached,
        groups=groups,traces=sorted(rows,key=lambda r:-r['cells']),records=results,
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        assumptions=['Same conditional C1,Q2^128,zero-grinding,independent half-budget query screen.',
                     'Extension9/digest52 uninstantiated; fixed messages/GKR remain frozen.',
                     'Removed work is free: replacement constraints/proofs/links are omitted.',
                     'Trace comes from verification of ORIGINAL internal native proof, not our new compressed bundle.',
                     'GKR terminal replacement reduces external claims; does not itself remove inner symbolic evaluation.',
                     'Expected frontier is not deterministic size; no security or recursive-closure certificate.']),indent=2)+'\n')


if __name__=='__main__':main()
