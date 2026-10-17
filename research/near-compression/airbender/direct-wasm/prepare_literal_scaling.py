"""Prepare a Lean-generated literal fixture and independently check its AIR."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--reference-dir',required=True)
    ap.add_argument('--fixture',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();sys.path.insert(0,args.reference_dir)
    import prepared_code_table_air as air
    from reference import inspect
    cases=json.loads(args.fixture.read_text())['cases']
    if len(cases)!=1:raise ValueError('expected one scaling case')
    case=cases[0];spec,rows=air.make(case)
    original=inspect(spec['air'],rows,spec['public']);assert original['accepted'],original['violations'][:2]
    rejected=[]
    for index in (0,len(case['code'])//2,len(case['code'])-1):
        public=spec['public'][:];public[air.CODEPUB+air.RECORD*index+10]+=1
        assert not inspect(spec['air'],rows,public)['accepted']
        rejected.append('public code fee '+str(index))
    public=spec['public'][:];public[39]+=1
    assert not inspect(spec['air'],rows,public)['accepted'];rejected.append('published exit')
    bad=copy.deepcopy(rows);bad[0][-1][air.DONE]=0
    assert not inspect(spec['air'],bad,spec['public'])['accepted'];rejected.append('nonterminal final row')
    spec.update(source_packings=[16,16],aux_packings=[1,16],terminal_degree=1)
    args.output.mkdir(parents=True,exist_ok=True)
    def save(name,value): (args.output/name).write_text(json.dumps(value,separators=(',',':')))
    save('spec.json',spec)
    for i,table in enumerate(rows):save(f'source-{i:02d}-rows.json',{'rows':table})
    save('request.json',{k:case[k] for k in ('wasm_bytes','method','prepaid')})
    report=dict(status='PASS',label=case['label'],instructions=len(case['code']),
        rows=[len(t) for t in rows],widths=[t['width'] for t in spec['air']['tables']],
        public_fields=len(spec['public']),wasm_bytes=len(case['wasm_bytes']),
        fixture_sha256=hashlib.sha256(args.fixture.read_bytes()).hexdigest(),
        actual_run_call_outcome=case['actual_run_call_outcome'],rejected=rejected,
        scope='Actual Lean preparation/execution witness plus independent full-witness AIR check; cryptographic proof generated separately.')
    save('preparation-report.json',report);print(json.dumps(report))


if __name__=='__main__':main()
