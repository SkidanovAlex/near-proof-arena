"""Can the measured nibble SHA384 AIR fit the remaining recursive budget?

Frozen widths and omitted routing/auxiliary work make this a sensitivity screen,
not a generated full hash proof or a lower bound for all SHA384 constructions.
"""
import hashlib,json
from pathlib import Path
from screen_swirl_stacking_geometry import cost
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'results/swirl-security-review'
OUT=BASE/'sha384-recursion-screen'


def main():
    source=ROOT/'results/sha384-nibble64/prover-report.json'
    r=json.loads(source.read_text());branches=r['physical_opening_branches']
    measured=sum((1<<b['log_rows'])*b['width'] for b in branches)
    assert measured==27939408
    census=json.loads((BASE/'binary-root-bundle/hash-census.json').read_text())
    blocks=census['total_dynamic_blocks'];assert blocks==4649
    # Actual SHA512 schedule64/round80/endpoint1 and private boundary1 rows/block.
    selected=[(0,64),(2,80),(4,1),(20,1)]
    unpadded_source=sum(branches[i]['width']*rows*blocks for i,rows in selected)
    unpadded_with_aux=sum((branches[i]['width']+branches[i+1]['width'])*rows*blocks for i,rows in selected)
    padded_with_aux=sum((branches[i]['width']+branches[i+1]['width'])*(1<<(rows*blocks-1).bit_length()) for i,rows in selected)
    fixed=sum((1<<branches[i]['log_rows'])*(branches[i]['width']+branches[i+1]['width']) for i in range(6,20,2))
    assert sum((branches[i]['width']+branches[i+1]['width'])*(1<<(rows*64-1).bit_length()) for i,rows in selected)+fixed==measured
    scenarios={'source_only_unpadded_no_fixed_tables':unpadded_source,
               'source_and_aux_unpadded_no_fixed_tables':unpadded_with_aux,
               'frozen_padded_all_tables':padded_with_aux+fixed}
    records=[]
    for name,cells in scenarios.items():
        options=[]
        for h in range(15,26):
            for rate in range(2,28-h):
                for fold in range(1,9):
                    for terminal in range(1,13):
                        rounds=(h-terminal+fold-1)//fold
                        if h-rounds*fold<0:continue
                        options.append(cost(cells,0,h,rate,fold,terminal,9,52,public_cached=True,
                            constraint_fixed=161+1288,column_claims=0,framing_base=296))
        result=dict(name=name,cells=cells,best=min(options,key=lambda x:x['expected_frontier_bytes']),
                    below_target=sum(x['expected_frontier_bytes']<300000 for x in options),screened=len(options))
        records.append(result);print(name,cells,result['best']['expected_frontier_bytes'])
    paths=[source,BASE/'binary-root-bundle/hash-census.json',Path(__file__),Path(__file__).with_name('screen_swirl_stacking_geometry.py')]
    OUT.mkdir(exist_ok=True)
    (OUT/'report.json').write_text(json.dumps(dict(measured_64block_cells=measured,blocks=blocks,records=records,
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        limitations=['Frozen measured widths; multiplicity/degree/domain feasibility at larger scale NOT established.',
                     'Source-only scenario erases all auxiliary/routing/fixed-table costs and padding.',
                     'All nonhash verifier trace work and cached work omitted; prior fixed messages retained as an accounting template.',
                     'Same conditional C1,Q2^128,zero-grinding,independent half-budget query screen; not instantiated PQ128.',
                     'Expected frontier sizes not deterministic bounds; no universal SHA384 impossibility claim.']),indent=2)+'\n')


if __name__=='__main__':main()
