"""Prepare actual multiblock quotient witness; independent expression parity tests."""
import argparse,hashlib,json,random,sys,time
from pathlib import Path
import pq384_column_quotient as quotient

def main():
    p=argparse.ArgumentParser();p.add_argument('--input-directory',required=True);p.add_argument('--output-directory',required=True);p.add_argument('--reference-dir',required=True);a=p.parse_args()
    sys.path.append(str(Path(a.reference_dir).parent/'generic-air'));import reference as ref
    inp=Path(a.input_directory);out=Path(a.output_directory);out.mkdir(parents=True,exist_ok=True);spec=json.loads((inp/'spec.json').read_text());original=spec['air'];new,plans=quotient.quotient(original);spec['air']=new
    start=time.perf_counter();checks=0;cells=0;rng=random.Random(384);negatives=0
    for ti,(old,table,plan) in enumerate(zip(original['tables'],new['tables'],plans)):
        rows=json.loads((inp/f'source-{ti:02d}-rows.json').read_text())['rows'];reduced=quotient.project(rows,plan);assert quotient.lift(reduced,plan)==rows;cells+=len(rows)*len(rows[0])
        (out/f'source-{ti:02d}-rows.json').write_text(json.dumps({'rows':reduced},separators=(',',':')))
        # Arbitrary quotient witness, not only honest rows: old expanded and
        # rewritten expressions must agree even on invalid assignments.
        random_rows=[[rng.randrange(ref.P) for _ in range(plan['new_width'])] for _ in range(2)]
        expanded=quotient.lift(random_rows,plan)
        pairs=list(zip(old['constraints'],table['constraints']))
        for x,y in zip(old['interactions'],table['interactions']):pairs+=list(zip(x['mult']+x['msg'],y['mult']+y['msg']))
        for row in range(2):
            for e,f in pairs:
                assert ref.evaluate(e,expanded,row,spec['public'])==ref.evaluate(f,random_rows,row,spec['public']);checks+=1
        bad=[r.copy() for r in rows];ci,left,right=plan['equality_constraints'][0];bad[0][left]=(bad[0][left]+1)%ref.P
        try:quotient.project(bad,plan)
        except ValueError:negatives+=1
        else:raise AssertionError('inconsistent alias witness accepted')
    (out/'spec.json').write_text(json.dumps(spec,separators=(',',':')));(out/'plans.json').write_text(json.dumps(plans,separators=(',',':')))
    report=dict(status='PASS',original_widths=[p['old_width'] for p in plans],quotient_widths=[p['new_width'] for p in plans],
        removed_columns=[p['old_width']-p['new_width'] for p in plans],exact_witness_cells_checked=cells,arbitrary_witness_expression_parity_checks=checks,
        invalid_witness_projection_rejections=negatives,seconds=time.perf_counter()-start,original_spec_sha256=hashlib.sha256((inp/'spec.json').read_bytes()).hexdigest(),
        constraints_removed=0,degree_increase=0,scope='Column substitution refinement; independent proof of reduced AIR still required')
    (out/'preparation-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
