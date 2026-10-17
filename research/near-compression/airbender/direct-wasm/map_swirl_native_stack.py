"""Bind residual column pairs to verified layout metadata and native point.

Only terminal coefficients are evaluated; source trace and sumcheck/PCS proofs
are not supplied here.
"""
import gzip,hashlib,json,random
from pathlib import Path
import pq384_terminal_gkr as g
from swirl_weighted_stack_ext import kernels

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/swirl-security-review/native-stack-layout'


def main():
    prior=ROOT/'results/swirl-security-review'
    layouts=json.loads((OUT/'layouts.json').read_text())
    captures=[json.loads(x) for x in gzip.decompress((OUT/'point-capture.jsonl.gz').read_bytes()).splitlines()]
    assert len(captures)==1;c=captures[0]
    original=json.loads(gzip.decompress((prior/'native-controls/capture.jsonl.gz').read_bytes()).splitlines()[1])
    assert {k:v for k,v in c.items() if k not in ('r','l_skip')}==original
    openings=json.loads(gzip.decompress((prior/'native-dag-gkr/openings.json.gz').read_bytes()))
    pairs=json.loads(gzip.decompress((prior/'weighted-stack-kernel/native-pairs.json.gz').read_bytes()))
    assert [o['air'] for o in openings]==[x['air'] for x in c['traces']]
    lookup={};next_commit=1
    for t,o in enumerate(openings):
        lookup[o['air'],0]=(0,t)
        for part in range(1,len(o['parts'])):
            lookup[o['air'],part]=(next_commit,0);next_commit+=1
    assert next_commit==len(layouts)
    source_slices={};total_slices=0
    for commit,layout in enumerate(layouts):
        assert layout['l_skip']==c['l_skip'] and layout['height']&(layout['height']-1)==0
        ends={}
        for matrix,column,target,start,height in layout['slices']:
            key=(commit,matrix,column);assert key not in source_slices
            span=1<<max(height,c['l_skip'])
            assert start%span==0 and 0<=target<layout['width'] and start+span<=layout['height']
            assert start>=ends.get(target,0);ends[target]=start+span
            source_slices[key]=(target,start,height);total_slices+=1
    stack_log=layouts[0]['height'].bit_length()-1
    assert all(l['height']==layouts[0]['height'] for l in layouts)
    rng=random.Random(20261017);u=[tuple(rng.randrange(2013265921) for _ in range(4)) for _ in range(1+stack_log-c['l_skip'])]
    r=[tuple(x) for x in c['r']];coefficients=[[g.ZERO]*l['width'] for l in layouts]
    assignments=[]
    by_air={t['air']:t for t in c['traces']}
    for pair in pairs['pairs']:
        commit,matrix=lookup[pair['air'],pair['opening_part']]
        target,start,height=source_slices[commit,matrix,pair['column']]
        assert height-c['l_skip']==by_air[pair['air']]['n']
        a,b=kernels(c['l_skip'],stack_log,height,start,r,u)
        contribution=g.add(g.mul(tuple(pair['current_weight']),a),g.mul(tuple(pair['rotated_weight']),b))
        coefficients[commit][target]=g.add(coefficients[commit][target],contribution)
        assignments.append(dict(air=pair['air'],opening_part=pair['opening_part'],column=pair['column'],commit=commit,
                                target_column=target,start=start,height=height))
    # Ext4 implementation agrees with saved native base-field oracle.
    oracle=json.loads((prior/'weighted-stack-kernel/native-oracle.json').read_text())
    for case in oracle:
        a,b=kernels(case['l'],case['stack'],case['height'],case['start'],[g.base(13+i*7) for i in range(4)],[g.base(23+i*11) for i in range(4)])
        assert g.add(g.mul(g.base(17),a),g.mul(g.base(29),b))==g.base(case['value'])
    report=dict(status='NATIVE_POINT_LAYOUT_AND_RESIDUAL_PLACEMENT_CHECKED',l_skip=c['l_skip'],stack_log=stack_log,
        commitment_widths=[l['width'] for l in layouts],all_source_slices=total_slices,mapped_pairs=len(assignments),
        short_pairs=sum(x['height']<c['l_skip'] for x in assignments),native_kernel_checks=len(oracle),
        terminal_coefficients=coefficients,evaluation_point=u,assignments=assignments,
        input_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [OUT/'layouts.json',OUT/'point-capture.jsonl.gz',prior/'native-controls/capture.jsonl.gz',
             prior/'native-dag-gkr/openings.json.gz',prior/'weighted-stack-kernel/native-pairs.json.gz',
             prior/'weighted-stack-kernel/native-oracle.json']},
        limitations=['Evaluation point u is synthetic; not produced by a new weighted sumcheck.',
                    'Committed source matrices not reconstructed; no final opening equality claimed.',
                    'Original proof and openings still needed; no replacement PCS/transcript/QROM theorem.'])
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print({k:v for k,v in report.items() if k not in ('assignments','terminal_coefficients','evaluation_point')})


if __name__=='__main__':main()
