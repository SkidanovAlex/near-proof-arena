import argparse,copy,gzip,json,random
from pathlib import Path
import pq384_ext8_reference as f
import pq384_ext8_input_weights as w
import ext8_pooled_weights as pool
from ext8_coefficient_claim_contract import coefficient_claim as old_claim


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    rng=random.Random(92501);scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8));claims=mles=padding=0
    for bank_log in (1,2,3):
        for packing in (1,2,4):
            rows=[[rng.randrange(f.P) for _ in range(7)] for _ in range(1<<bank_log)]
            terms=[dict(offset=1,width=2,row_point=[scalar() for _ in range(bank_log)],current=[scalar(),scalar()],next=[scalar(),scalar()]),
                   dict(offset=4,width=2,row_point=[scalar() for _ in range(bank_log-1)],current=[scalar(),scalar()],next=[scalar(),scalar()])]
            expected=pool.direct_claim(rows,terms)
            assert pool.coefficient_claim(rows,terms,packing)==expected;claims+=1
            for start in range(0,7,packing):
                u=[scalar() for _ in range(bank_log+packing.bit_length()-1)]
                assert w.mle(pool.lane_weights(terms,bank_log,7,start,packing),u)==pool.lane_weight_mle(terms,bank_log,7,start,packing,u);mles+=1
            changed=copy.deepcopy(rows)
            for row in changed:row[0]=rng.randrange(f.P);row[3]=rng.randrange(f.P);row[6]=rng.randrange(f.P)
            for row in changed[1<<(bank_log-1):]:row[4]=rng.randrange(f.P);row[5]=rng.randrange(f.P)
            assert pool.coefficient_claim(changed,terms,packing)==expected;padding+=1
    # A concrete failure of padding the point and using the physical cyclic shift.
    rows=[[10],[20],[99],[77]]
    term=dict(offset=0,width=1,row_point=[f.ONE],current=[f.ZERO],next=[f.ONE])
    correct=pool.coefficient_claim(rows,[term],1)
    naive=old_claim(rows,dict(log_rows=2,width=1,packing=1,row_point=[f.ONE,f.ZERO],lanes=[([f.ZERO],[f.ONE])]))
    assert correct==f.base(10) and naive==f.base(99)
    rejects=[]
    for name,mutate in [('offset',lambda x:x.update(offset=-1)),('width',lambda x:x.update(width=2)),
                        ('height',lambda x:x.update(row_point=[f.ZERO]*3)),('weights',lambda x:x.update(current=[])),
                        ('scalar',lambda x:x.update(next=[(f.P,0,0,0,0,0,0,0)]))]:
        bad=copy.deepcopy(term);mutate(bad)
        try:pool.coefficient_claim(rows,[bad],1)
        except ValueError:rejects.append(name)
        else:raise AssertionError(name)
    spec=json.loads(gzip.decompress(Path('results/ext8-affine-derived-q309/statement.json.gz').read_bytes()))['spec']
    banks=pool.phase_layout(spec)
    assert [(b['phase'],b['log_rows'],b['width']) for b in banks]==[('source',11,7091),('auxiliary',11,296),('source',5,179)]
    result=dict(status='PASS',coefficient_claim_cases=claims,compact_beta_cases=mles,unused_cells_cases=padding,
                rejections=rejects,naive_cyclic_shift_counterexample=dict(correct=10,naive=99),actual_phase_banks=banks,
                scope='Pooled coefficient-functional prototype only. No pooled PCS/commitment/transcript integration or actual pooled proof-size/security claim. Compact-beta formula checked numerically; formal specialization remains separate.')
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
