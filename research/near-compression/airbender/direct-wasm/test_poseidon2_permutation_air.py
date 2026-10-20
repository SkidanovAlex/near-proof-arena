"""Canonical AIR evaluation and independent pinned Rust permutation parity."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import poseidon2_permutation_air as candidate
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'generic-air'))
import reference
import scheduled_bus_whir as algebra


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--oracle',type=Path,required=True);args=parser.parse_args()
    compiled=candidate.compile_permutation(6);table=compiled['table'];P=candidate.P
    rng=random.Random(20261017)
    inputs=[[0]*32,[1]*32,[P-1]*32]+[[int(i==j) for i in range(32)] for j in range(32)]
    inputs += [[rng.randrange(P) for _ in range(32)] for _ in range(8)]
    # Literal upstream known-answer test, separately parsed from pinned source.
    source=gzip.decompress((candidate.ROOT/'results/hash-architecture-review/upstream/Plonky3-baby-bear_src_poseidon2.rs.gz').read_bytes()).decode()
    test=source.split('fn test_default_babybear_poseidon2_width_32()',1)[1].split('\n    }',1)[0]
    arrays=re.findall(r'BabyBear::new_array\(\[(.*?)\]\)',test,re.S)
    known=[[int(x) for x in re.findall(r'\d+',a)] for a in arrays]
    assert len(known)==2 and all(len(a)==32 for a in known)
    inputs.append(known[0])
    raw='\n'.join(' '.join(map(str,row)) for row in inputs)+'\n'
    result=subprocess.run([str(args.oracle.resolve())],input=raw,text=True,capture_output=True,check=True)
    expected=[[int(x) for x in line.split()] for line in result.stdout.splitlines()]
    assert len(expected)==len(inputs) and expected[-1]==known[1]
    rows=[candidate.witness(compiled,x) for x in inputs]
    assert all([row[c] for c in compiled['output_columns']]==out for row,out in zip(rows,expected))
    # Canonical schema/evaluator checks the table as actual np-air-v2 rows.
    padded=rows+[rows[0]]*((1<<table['maxLog'])-len(rows))
    air=dict(format='np-air-v2',numBuses=0,numPub=0,maxPub=0,pubSegs=[],tables=[table])
    reference.schema(air)
    checked=reference.check(air,[padded],[])
    residuals=sum(len(row) for row in checked['residuals'][0])
    assert residuals==64*2074
    # Verify causal assignment order structurally. Every intermediate/output
    # coordinate is constrained, then corrupt it and check its owner equation
    # using the independent canonical evaluator rather than witness evaluation.
    def refs(e):
        if e[0]=='v':return {e[1]}
        if e[0]=='c':return set()
        return set().union(*(refs(x) for x in e[1:]))
    negatives=0
    for i,e in enumerate(compiled['assignments'],32):
        assert all(c<i for c in refs(e))
        row=rows[-2].copy();row[i]=(row[i]+1)%P
        assert reference.evaluate(table['constraints'][i-32],[row,row],0,[])!=0
        negatives+=1
    for i in range(32):
        row=rows[-2].copy();row[i]=(row[i]+1)%P
        assert any(reference.evaluate(e,[row,row],0,[]) for e in table['constraints'])
        negatives+=1
    degree=algebra.table_degree(table,0)
    out=candidate.ROOT/'results/poseidon2-permutation-layout'
    spec_raw=json.dumps(air,sort_keys=True,separators=(',',':')).encode()
    (out/'air.json.gz').write_bytes(gzip.compress(spec_raw,mtime=0))
    vectors=dict(inputs=inputs,outputs=expected)
    (out/'vectors.json').write_text(json.dumps(vectors,indent=2)+'\n')
    pins=[Path(__file__),Path(candidate.__file__),out/'air.json.gz',out/'vectors.json',out/'sources.json',
          candidate.ROOT/'results/hash-architecture-review/sources.json',
          candidate.ROOT/'airbender/direct-wasm/poseidon2-oracle/Cargo.toml',
          candidate.ROOT/'airbender/direct-wasm/poseidon2-oracle/Cargo.lock',
          candidate.ROOT/'airbender/direct-wasm/poseidon2-oracle/src/main.rs']
    source_manifest=json.loads((out/'sources.json').read_bytes())
    for item in source_manifest['files']:
        snapshot=candidate.ROOT/item['snapshot'];raw=gzip.decompress(snapshot.read_bytes())
        assert hashlib.sha256(raw).hexdigest()==item['raw_sha256']
        assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==item['snapshot_sha256']
        pins.append(snapshot)
    pins += [Path(reference.__file__),Path(algebra.__file__),
             candidate.ROOT/'results/hash-architecture-review/upstream/Plonky3-baby-bear_src_poseidon2.rs.gz']
    report=dict(status='POSEIDON2_32_PERMUTATION_AIR_PARITY',upstream_commit='f98331687e47106a64ab82a77e2e1d0d66c9161b',
        width=table['width'],constraints_per_row=len(table['constraints']),reported_table_degree=degree,
        independent_permutations=len(inputs),known_answer_matches=True,canonical_rows_checked=len(padded),
        canonical_constraint_evaluations=residuals,mutation_rejections=negatives,
        assignment_order_checked=True,output_columns=compiled['output_columns'],
        rows_per_permutation=1,full_rounds=8,partial_rounds=30,sbox_exponent=7,
        rows_per_hypothetical_pair_hash=2,source_cells_per_hypothetical_pair_hash=2*table['width'],
        oracle_binary_sha256=hashlib.sha256(args.oracle.read_bytes()).hexdigest(),
        compiler_lean_certified=False,pq128_certified=False,sponge_implemented=False,
        scope='Complete permutation relation in one wide row; canonical inputs and outputs share the same row. No call binding, sponge framing/padding, transcript, Merkle compression, ZK, recursive proof, quantum security, or NEAR certificate. Pair-hash count imports the earlier hypothetical width32/capacity13/rate19 wrapper; it is not implemented.',
        sha256={str(p.relative_to(candidate.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in pins})
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
