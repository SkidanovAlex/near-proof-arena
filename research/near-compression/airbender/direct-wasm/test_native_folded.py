"""Exact native parity; imports trusted reference modules from supplied root."""
import argparse, json, os, random, sys, time
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--library',required=True)
    ap.add_argument('--report',required=True);args=ap.parse_args()
    reference=Path(args.reference_dir).resolve();sys.path.append(str(reference));os.environ['NEAR_NATIVE_FOLDED_LIB']=args.library
    import native_folded as native
    import heterogeneous_bus_whir as protocol
    import folded_prover as python
    from verify_whir_toy import P,base,ext
    results=reference.parents[1]/'results';rng=random.Random(90417)
    random_ext=lambda:tuple(rng.randrange(P) for _ in range(4))
    air=json.loads((results/'d1-air.json').read_text());lib=native.library();cases=[]
    start=time.perf_counter()
    for ti,table in enumerate(air['tables']):
        alpha,gamma,mixing=random_ext(),random_ext(),random_ext();tau=[random_ext(),random_ext()]
        shape=protocol.aux.layout(table);finals=[random_ext() for _ in range(shape['finals'])]
        public=[rng.randrange(P) for _ in range(37)] # includes actual public default-zero reads
        width=table['width']+4*shape['aux_columns']
        rows=[[rng.randrange(P) for _ in range(width)] for _ in range(4)]
        spec={'air':{'tables':[table]},'public':public};degree=protocol.table_degree(table,air['numPub'])
        program=native.compile_weighted(table,public,alpha,gamma,finals,mixing,protocol)
        cur=[[base(v) for v in row] for row in rows];nxt=cur[1:]+cur[:1];point=[]
        with native.NativeTable(rows,program,tau,lib) as state:
            for i in range(2):
                actual=state.values(degree+2);expected=[]
                from verify_whir_toy import ZERO,add
                for node in range(degree+2):
                    total=ZERO;r=base(node)
                    for pair in range(len(cur)//2):
                        at=point+[r]+python.boolean_point(pair,1-i)
                        c=[python.affine(a,b,r) for a,b in zip(cur[2*pair],cur[2*pair+1])]
                        g=[python.affine(a,b,r) for a,b in zip(nxt[2*pair],nxt[2*pair+1])]
                        total=add(total,protocol.weighted(spec,0,alpha,gamma,finals,mixing,tau,at,c,g))
                    expected.append(total)
                assert actual==expected,(ti,i)
                r=random_ext();state.fold(r);cur=python.fold_rows(cur,r);nxt=python.fold_rows(nxt,r);point.append(r)
        cases.append({'table':ti,'source_constraints':len(table['constraints']),'program_nodes':len(program)//7,'degree':degree})
    parity_seconds=time.perf_counter()-start
    spec=json.loads((results/'heterogeneous-bus-spec.json').read_text());proof=json.loads((results/'heterogeneous-bus-proof.json').read_text())
    roots=json.loads((results/'heterogeneous-bus-statement.json').read_text())['roots']
    source=[json.loads((results/f'heterogeneous-bus-source-{i}.json').read_text())['rows'] for i in range(2)]
    coords=[json.loads((results/f'heterogeneous-bus-aux-{i}.json').read_text())['rows'] for i in range(2)]
    auxiliary=[[[tuple(row[j:j+4]) for j in range(0,len(row),4)] for row in rows] for rows in coords]
    finals=[[ext(v) for v in fs] for fs in proof['finals']]
    start=time.perf_counter();got,handoffs=native.prove(spec,roots,source,proof['aux_roots'],auxiliary,finals);native_seconds=time.perf_counter()-start
    for ti,part in enumerate(got['tables']):
        part['openings']=proof['tables'][ti]['openings']
        for branch in range(2):assert handoffs[ti][branch]==json.loads((results/f'heterogeneous-bus-handoff-{ti}-{branch}.json').read_text())
    assert got==proof;assert protocol.verify(got,spec,roots)
    report={'status':'PASS','actual_d1_tables':cases,'actual_d1_random_point_parity_seconds':parity_seconds,
            'saved_real_pcs_proof_and_handoff_identical':True,'independent_verifier_accepted':True,
            'tiny_native_prover_seconds':native_seconds,
            'limitations':['D1 parity uses4randomrows per actualtable, not fullD1proof.','Transcript and shift reduction still Python.','No security level or formal Rust refinement claim.']}
    Path(args.report).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
