"""Exact literal AST parity for every supported local-count parameter."""
import argparse, hashlib, json
from pathlib import Path
from prepared_typed_air import air
from generate_prepared_typed_literal import generate
p=argparse.ArgumentParser();p.add_argument('--export',required=True,type=Path);p.add_argument('--report',required=True,type=Path);a=p.parse_args()
source=Path(__file__).resolve().parents[2]/'NearCompression/PreparedTypedLiteral.lean'
assert source.read_text()==generate(),'generated literal source differs'
actual=json.loads(a.export.read_text());assert len(actual)==5
cases=[]
for count,got in enumerate(actual):
    want=air(19,count);counts=[]
    for table in want['tables']:
        original=len(table['constraints'])
        automatic=[['*',e,['+',e,['-',['c',1]]]] for it in table['interactions'] for e in it['mult']]
        table['constraints']+=automatic
        counts.append(dict(user=original,automatic=len(automatic)))
    assert got==want,('exact literal mismatch',count)
    cases.append(dict(local_count=count,constraints=counts))
report=dict(status='PASS',cases=cases,all_interactions_public_segments_equal=True,
 source_sha384=hashlib.sha384(source.read_bytes()).hexdigest(),
 scope='Exact exported source parity; AIR-to-step semantic refinement remains separate.')
a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
