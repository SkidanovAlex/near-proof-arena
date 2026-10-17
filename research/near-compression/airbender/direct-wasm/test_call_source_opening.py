"""Compare actual call PCS branch weights with Lean source-opening semantics."""
import argparse,gzip,hashlib,json,subprocess
from pathlib import Path
import sha384_call_pcs as cp


def main():
    p=argparse.ArgumentParser();p.add_argument('--output-directory',type=Path,required=True);a=p.parse_args()
    package=Path(__file__).resolve().parents[2];out=a.output_directory;out.mkdir(parents=True,exist_ok=True)
    source=package/'results/ext8-linked-calls';read=lambda f:json.loads(f.read_text())
    st=json.loads(gzip.decompress((source/'statement.json.gz').read_bytes()));rows=read(source/'rows.json');calls=read(source/'calls.json')
    receipt=read(package/'results/ext8-node-batch/expected-use.json');g=cp.g
    proof=json.loads(gzip.decompress((package/'results/ext8-call-pcs/proof.json.gz').read_bytes()))
    layout,_,binding,_=cp.compile_layout(st,receipt,calls);ob=g.verify(layout,binding,proof['gkr']);branches=cp.branches(st,ob)
    rowlog=st['spec']['log_rows'][3];inputlog=layout['input_size'].bit_length()-1;width=179
    assert all(layout['private_capacity']<=int(i)<layout['input_size'] for i in layout['constants'])
    fixture=dict(row_log=rowlog,column_log=inputlog-rowlog,width=width,rows=rows,
        constants=[[int(i),v] for i,v in layout['constants'].items()],queries=[dict(point=p,scale=w) for p,w in ob['queries']])
    path=out/'input.json';path.write_text(json.dumps(fixture,separators=(',',':')))
    output=out/'lean-output.json'
    run=subprocess.run(['lake','env','lean','--run','ReplayCallSource.lean',str(path),str(output)],cwd=package,text=True,capture_output=True,timeout=120)
    (out/'lean.log').write_text(run.stdout+run.stderr);run.check_returncode()
    lean=read(output);assert len(lean)==len(branches)==2
    total=g.ZERO;known=g.ZERO;full=g.ZERO;high_bit_changes=0
    n=1<<rowlog
    for result,branch,(point,scale) in zip(lean,branches,ob['queries']):
        assert branch['root']==st['roots'][3] and branch['row_point']==point[:rowlog]
        flat=[w for lane in branch['lanes'] for w in lane[0]]
        assert [list(w) for w in flat[:width]]==result['coefficients']
        assert all(w==g.ZERO for w in flat[width:])
        assert all(w==g.ZERO for lane in branch['lanes'] for w in lane[1])
        dot=g.ZERO
        for c,w in enumerate(flat[:width]):dot=g.add(dot,g.mul(w,g.mle([g.base(row[c]) for row in rows],point[:rowlog])))
        assert list(dot)==result['source']
        total=g.add(total,dot);known=g.add(known,tuple(result['known']));full=g.add(full,tuple(result['full']))
        # Omitting the extra input bit is an incorrect adapter, even though all
        # source columns lie below the compiler's private column capacity.
        for col,w in enumerate(flat[:width]):
            truncated=scale
            for bit,r in enumerate(point[rowlog:rowlog+8]):truncated=g.mul(truncated,r if (col>>bit)&1 else g.sub(g.ONE,r))
            high_bit_changes+=truncated!=w
    assert total==ob['private_claim'] and g.sub(full,known)==ob['private_claim']
    assert high_bit_changes>0
    report=dict(status='PASS',rows=n,width=width,input_log=inputlog,row_log=rowlog,column_log=inputlog-rowlog,
        all_column_weights_match_lean=True,all_next_and_padding_weights_zero=True,same_source_root=True,
        constant_subtracted_claim_matches=True,high_coordinate_truncation_changes=high_bit_changes,
        fixture_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),
        files={str(f.relative_to(package)):hashlib.sha256(f.read_bytes()).hexdigest() for f in
          [Path(__file__),package/'ReplayCallSource.lean',package/'NearCompression/CallSourceOpening.lean',Path(cp.__file__)]},
        scope='General source-MLE and constant-subtraction identities are proved in Lean; actual two-query branch weights and claims match a replay over the diagnostic field. Source rows are used only for this regression. This is algebraic opening-obligation binding, not Merkle/PCS cryptographic soundness or QROM certification.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
