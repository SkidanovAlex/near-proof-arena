"""Exact shape accounting; does not infer full transcript or proof-size savings."""
import hashlib
import json
from pathlib import Path
import ext8_closed_derived_switch as closed
import ext8_code_switch_stage as old
from pq384_primitives import PREFIX

ROOT=Path(__file__).resolve().parents[2]


def blocks(tag,lengths):
    size=len(PREFIX)+4+len(tag)+4+sum(8+n for n in lengths)
    return (size+17+127)//128


def main():
    paths=['results/full-hybrid-verifier.json','results/structured-verifier-states.json','results/ext8-switch-execution-q309/config.json','results/switch-full-verifier-hash-work.json']
    hybrid,shadow,config,work=[json.loads((ROOT/p).read_text()) for p in paths]
    assert hybrid['fresh_dense_and_hybrid_verified'] and hybrid['ordered_hash_calls_compared']==104839
    dense_terms=sum(e['degree']*e['points'] for e in hybrid['events'] if e['kind']=='inject' and not e['structured'])
    expansion_terms=sum(e['degree']*e['terms'] for e in hybrid['events'] if e['kind']=='materialize')
    terms=fold_updates=0
    for e in hybrid['events']:
        if e['kind']=='inject' and e['structured']:terms+=e['points']
        if e['kind']=='fold' and e['structured']:fold_updates+=terms
        if e['kind']=='materialize':assert e['terms']==terms
    state=dict(degree=131072,blowup=config['child_blowup'],fold_bits=config['child_fold_bits'],namespace='00'*48,parent='00'*48,root='00'*48)
    stage_blocks=[]
    for step in config['tail_steps']:
        cfg=old.follow_config(state,step)
        original=blocks(old.PROFILE.encode(),[len(old.canonical_json(cfg)),32*state['degree'],32])
        cfg['profile']=closed.STAGE_PROFILE
        candidate=blocks(closed.STAGE_PROFILE.encode(),[len(closed.DERIVATION),len(old.canonical_json(cfg)),32])
        stage_blocks.append(dict(degree=state['degree'],baseline_blocks=original,closed_candidate_blocks=candidate))
        state.update(degree=state['degree']>>state['fold_bits'],blowup=step['next_blowup'],fold_bits=step['next_fold_bits'])
    old_blocks=sum(s['baseline_blocks'] for s in stage_blocks);new_blocks=sum(s['closed_candidate_blocks'] for s in stage_blocks)
    assert old_blocks==work['measurement']['tags'][old.PROFILE]['unique_blocks']
    report=dict(status='CLOSED_HYBRID_SHAPE_COST_ACCOUNTED',baseline_injection_coefficient_terms=shadow['dense_injection_coefficient_terms'],
        hybrid_materialization_coefficient_terms=expansion_terms,hybrid_dense_injection_coefficient_terms=dense_terms,
        structured_geometric_fold_updates=fold_updates,stage_start_hash_blocks=stage_blocks,
        baseline_stage_blocks=old_blocks,candidate_stage_blocks=new_blocks,
        unchanged_other_work_counterfactual_blocks=work['measurement']['totals']['unique_blocks']-old_blocks+new_blocks,
        decision='Hybrid derivation removes large dense-functional work, but stage-start omission alone leaves about205000hash compression blocks if other recorded work is held fixed. Keep the prototype separate; next evaluate remaining hash architecture and full joint-verifier geometry/security rather than generate a large proof solely for this optimization.',
        scope='Hybrid loop counts exclude temporary expansions required by baseline vector hashing; they describe the closed-profile candidate on this shape, not all work in the compatibility replay. Not field-operation or runtime ratios: native injection distinguishes base and extension points. Candidate stage framing uses fixed-width placeholder digests and exact configuration lengths; new challenges and hash sharing elsewhere can change, so remaining-work figure is a counterfactual, not a measured new protocol or rigorous global bound. Excludes full-verifier arithmetic beyond functional state, application routing, outer proof size and PQ128 soundness.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(closed.__file__),Path(old.__file__)]+[ROOT/p for p in paths]})
    (ROOT/'results/closed-hybrid-work.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
