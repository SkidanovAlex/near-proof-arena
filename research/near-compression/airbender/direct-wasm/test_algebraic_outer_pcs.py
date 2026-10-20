"""Independent finite schedule enumeration and domain rejection controls."""
import json
import math
from fractions import Fraction as F
import screen_algebraic_outer_pcs as s


def all_costs(degree,rate,budget,extension):
    if not s.valid_domain(degree,rate):return
    if degree<=64:yield 4*extension*degree
    for k in range(1,min(8,degree.bit_length()-1)+1):
        edge=s.cost.stage(degree,rate,k,'johnson',(8*extension,),budget,extension,64)
        for nr in s.RATES:
            for child in all_costs(degree>>k,nr,budget,extension):
                yield edge['expected_bytes']+child


def main():
    tested=enumerated=0
    for degree,rate in [(8,4),(32,16),(128,64)]:
        for extension in (8,12):
            costs=list(all_costs(degree,rate,12,extension))
            selected,path=s.optimize(degree,rate,12,extension,64)
            assert math.isclose(selected,min(costs),abs_tol=1e-8)
            if path:s.validate_path(path)
            enumerated+=len(costs);tested+=1
    assert s.valid_domain(1<<25,4)
    assert not s.valid_domain(1<<25,16)
    assert s.optimize(1<<25,16,262,12,64)==(float('inf'),())
    r=json.loads((s.ROOT/'results/poseidon2-permutation-layout/outer-pcs-screen.json').read_bytes())
    for record in r['records']:
        path=record['best']['path'];s.validate_path(path)
        assert record['optimistic_source_only']['source_only_expected_bytes']<=record['best']['source_only_expected_bytes']
        assert record['source_only_already_exceeds_whole_bundle']==(record['optimistic_source_only']['source_only_expected_bytes']>=300000)
        prefix=record['relaxed_source_only_full_error_budget'];stage=prefix['first_stage']
        factor=F(21,20*math.isqrt(stage['rate']));scale=2**(256+record['assumed_log2_C'])
        assert scale*factor**stage['queries']<=F(1,2)
        assert scale*factor**(stage['queries']-1)>F(1,2)
        assert record['one_unit_algebra_floor_exceeds_half']==(F(record['one_unit_algebra_QROM_floor'])>F(1,2))
        assert record['relaxed_all_stages_full_error_budget']['expected_optimistic_bytes']>=300000
        assert s.hash_term(record['hash_bytes'],record['assumed_log2_C'])<=F(1,4)
        if record['hash_bytes']!=64:
            assert s.hash_term(record['hash_bytes']-1,record['assumed_log2_C'])>F(1,4)
        else:
            assert record['relaxed_expected_gate_rejects']
        ledger=record['partial_security_ledger']
        assert ledger['partial_within_half_success']==(F(ledger['partial_QROM_bound'])<=F(1,2))
    assert r['survivors_of_expected_byte_and_partial_ledger_screen']==0
    print(json.dumps(dict(status='PASS',exhaustive_schedule_cases=tested,
        enumerated_schedule_costs=enumerated,invalid_lde_domain_rejected=True,
        conditional_fraction_decisions_checked=True,
        scope='Finite conditional-cost arithmetic only; no soundness theorem or security certificate.')))


if __name__=='__main__':main()
