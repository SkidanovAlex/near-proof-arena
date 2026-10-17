"""Domain-constrained outer code-switch screen for the concrete permutation AIR.

Uses existing *conditional* Johnson/MCA/QROM arithmetic, not a security theorem.
All permutation source cosets are priced; missing full-verifier work costs zero.
"""
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import screen_weighted_code_switch as cost
from screen_larger_field_code_switch import ledger
from pq384_ext8_reference import P

ROOT=Path(__file__).resolve().parents[2]
DOMAIN_CAP=1<<27
RATES=(4,16,64)


def valid_domain(degree,rate):
    return degree>0 and degree&(degree-1)==0 and rate in RATES and degree*rate<=DOMAIN_CAP


@lru_cache(None)
def optimize(degree,rate,budget,extension,hash_bytes):
    if not valid_domain(degree,rate):
        return float('inf'),()
    best=(4*extension*degree,()) if degree<=64 else (float('inf'),())
    for k in range(1,min(8,degree.bit_length()-1)+1):
        edge=cost.stage(degree,rate,k,'johnson',(8*extension,),budget,extension,hash_bytes)
        child_degree=degree>>k
        for next_rate in RATES:
            tail,path=optimize(child_degree,next_rate,budget,extension,hash_bytes)
            if edge['expected_bytes']+tail<best[0]:
                best=(edge['expected_bytes']+tail,(dict(edge,next_rate=next_rate),)+path)
    return best


def screen(rows,width,extension,budget,hash_bytes=64):
    assert rows>1 and rows&(rows-1)==0 and width>0
    candidates=[];excluded=0
    for log_packing in range((width-1).bit_length()+1):
        packing=1<<log_packing;degree=rows*packing
        for rate in RATES:
            if not valid_domain(degree,rate):
                excluded+=1;continue
            widths=(8*((width+packing-1)//packing),)
            for k in range(1,min(8,degree.bit_length()-1)+1):
                edge=cost.stage(degree,rate,k,'johnson',widths,budget,extension,hash_bytes)
                for next_rate in RATES:
                    tail,path=optimize(degree>>k,next_rate,budget,extension,hash_bytes)
                    if tail==float('inf'):continue
                    # Execution frame + source root + local degree2 sumcheck,
                    # plus initial weighted sumcheck. No GKR/aux/routing cost.
                    fixed=8+hash_bytes+4*extension*4*(rows.bit_length()-1)+12*extension*(degree.bit_length()-1)
                    candidates.append(dict(packing=packing,initial_rate=rate,degree=degree,
                        fixed_bytes=fixed,source_pair_bytes=widths[0],
                        source_only_expected_bytes=fixed+edge['expected_bytes'],
                        expected_optimistic_bytes=fixed+edge['expected_bytes']+tail,
                        path=[dict(edge,next_rate=next_rate)]+list(path)))
    best=min(candidates,key=lambda c:c['expected_optimistic_bytes'])
    source_only=min(candidates,key=lambda c:c['source_only_expected_bytes'])
    prefix={k:source_only[k] for k in ('packing','initial_rate','degree','fixed_bytes','source_pair_bytes','source_only_expected_bytes')}
    prefix['first_stage']=source_only['path'][0]
    return best,len(candidates),excluded,prefix


def validate_path(path):
    assert path
    for i,s in enumerate(path):
        assert valid_domain(s['degree'],s['rate'])
        assert valid_domain(s['degree']>>s['skipped'],s['next_rate'])
        assert s['folded_domain']==s['degree']*s['rate']//(1<<s['skipped'])
        if i+1<len(path):
            assert path[i+1]['degree']==s['degree']>>s['skipped']
            assert path[i+1]['rate']==s['next_rate']
    assert path[-1]['degree']>>path[-1]['skipped']<=64


def hash_term(hash_bytes,logC):
    Q=2**128
    return F(3*(2**logC)*(Q**3+Q),2**(8*hash_bytes))


def adjusted_ledger(path,extension,logC,hash_bytes):
    result=ledger(path,extension,logC)
    value=F(result['partial_QROM_bound'])-hash_term(64,logC)+hash_term(hash_bytes,logC)
    result.update(partial_QROM_bound=str(value),partial_QROM_bound_float=float(value),
                  partial_within_half_success=value<=F(1,2),hash_term=str(hash_term(hash_bytes,logC)))
    return result


def main():
    paths=['results/poseidon2-permutation-layout/workload.json','results/poseidon2-permutation-layout/report.json']
    work,layout=[json.loads((ROOT/p).read_bytes()) for p in paths]
    for data in (work,layout):
        for p,expected in data['sha256'].items():
            assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==expected
    rows,width=work['padded_permutation_rows'],layout['width']
    records=[]
    for extension in (8,10,12):
        for logC,budget in ((0,262),(8,270)):
            minimal_hash_bytes=next(n for n in range(1,65) if hash_term(n,logC)<=F(1,4))
            for hash_bytes in (64,minimal_hash_bytes):
                best,count,excluded,prefix=screen(rows,width,extension,budget,hash_bytes)
                validate_path(best['path'])
                trials=[cost.simulate(best['path'],19300+i,extension,hash_bytes) for i in range(16)]
                sizes=[t['bytes']+best['fixed_bytes'] for t in trials]
                partial=adjusted_ledger(best['path'],extension,logC,hash_bytes)
                # Give the first query term the ENTIRE nominal success allowance:
                # C*Q^2*factor^q <= 1/2. cost.queries bounds factor^q directly.
                relaxed_all,_,_,relaxed=screen(rows,width,extension,257+logC,hash_bytes)
                arithmetic_floor=F((2**logC)*(2**256),P**extension)

                records.append(dict(extension=extension,hash_bytes=hash_bytes,assumed_log2_C=logC,
                    isolated_query_bits=budget,searched_candidates=count,invalid_source_domain_shapes_excluded=excluded,
                    best=best,optimistic_source_only=prefix,
                    relaxed_source_only_full_error_budget=relaxed,
                    relaxed_all_stages_full_error_budget=relaxed_all,
                    one_unit_algebra_QROM_floor=str(arithmetic_floor),
                    one_unit_algebra_floor_exceeds_half=arithmetic_floor>F(1,2),
                    relaxed_expected_gate_rejects=(relaxed['source_only_expected_bytes']>=300000 or arithmetic_floor>F(1,2)),
                    min_simulated_bytes=min(sizes),max_simulated_bytes=max(sizes),simulated_sizes=sizes,
                    partial_security_ledger=partial,optimistic_whole_bundle_headroom_bytes=299999-best['expected_optimistic_bytes'],
                    source_only_already_exceeds_whole_bundle=prefix['source_only_expected_bytes']>=300000,
                    remaining_assumptions_certified=False,implemented_profile=False))
    report=dict(status='ALGEBRAIC_LAYOUT_OUTER_PCS_CONDITIONAL_SCREEN',rows=rows,width=width,
        base_field=P,base_field_domain_cap=DOMAIN_CAP,records=records,
        survivors_of_expected_byte_and_partial_ledger_screen=sum(
            r['best']['expected_optimistic_bytes']<300000 and r['partial_security_ledger']['partial_within_half_success'] for r in records),
        scope='One source tree for the measured single-row permutation layout, old-input byte-wrapper workload. All first-stage cosets, tail leaf/frontier messages, stage headers, terminal disclosure and initial weighted/local sums priced. Base-field LDE domain checked at source and every destination. Sizes are expectations plus16simulations, not measured proofs or universal bounds. GKR, auxiliary integration, sponge/encoding/call binding, other verifier arithmetic and fullNEAR cost zero.',
        security_scope='Reuses uninstantiated Johnson/MCA/weighted composition and C*(Q^2*epsilon+3*(Q^3+Q)/2^h) sensitivity at Q=2^128,C=1/256. Partial ledger excludes local/GKR/bus/initial reduction errors and concrete compiler/extraction/QROM proofs. Failure of this upper bound is not an attack; passing it is not certification. Ext10/12 and49/50/64-byte outer hashes are projections, not implemented profiles. Short digests are the minimum whole-byte sizes giving the nominal hash term at most1/4. Relaxed schedules give every query term the full1/2 allowance simultaneously and do not pass the summed ledger. Inner Poseidon2 M128 permutation has no PQ128 certificate.',
        decision='Reject scale-up of this layout/byte-wrapper/PCS family under the stated conditional model. Shorter digests can put the initial opening plus fixed reductions below300000B, so the512-bit prefix rejection is not general. Complete schedules still exceed budget, including an optimistic screen granting every stage the entire query-error allowance. Ext8 also fails the algebra term even at numerator1. Change committed workload or opening geometry before more schedule tuning. This is not a universal cryptographic impossibility result.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [Path(__file__),Path(cost.__file__),ROOT/'airbender/direct-wasm/screen_larger_field_code_switch.py',
             ROOT/'airbender/direct-wasm/report_code_switch_algebra.py',ROOT/'airbender/direct-wasm/report_code_switch_qrom.py']+[ROOT/p for p in paths]})
    (ROOT/'results/poseidon2-permutation-layout/outer-pcs-screen.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps([dict(extension=r['extension'],logC=r['assumed_log2_C'],hash_bytes=r['hash_bytes'],packing=r['best']['packing'],rate=r['best']['initial_rate'],
        expected_bytes=r['best']['expected_optimistic_bytes'],min_bytes=r['min_simulated_bytes'],max_bytes=r['max_simulated_bytes'],
        partial_pass=r['partial_security_ledger']['partial_within_half_success'],
        stages=[(s['degree'],s['rate'],s['skipped'],s['next_rate'],s['queries']) for s in r['best']['path']]) for r in records],indent=2))


if __name__=='__main__':main()
