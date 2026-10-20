"""Executable parity for canonical flat Ext4 operands and the certified tower."""
import hashlib,json,random,subprocess
from pathlib import Path
from check_whir_handoff import P,add,sub,mul
root=Path(__file__).resolve().parents[2]
out=root/'results/diagnostic-ext4-parity';out.mkdir(exist_ok=True)
basis=[tuple(int(i==j) for i in range(4)) for j in range(4)]
values=[(0,)*4,(1,)*4,(P-1,)*4,(0,1,P-1,P//2),*basis]
cases=[[a,b] for a in values for b in values]
rng=random.Random(384)
cases += [[tuple(rng.randrange(P) for _ in range(4)) for _ in range(2)] for _ in range(256)]
input_path=out/'inputs.json';output_path=out/'lean-output.json'
input_path.write_text(json.dumps(cases,separators=(',',':')))
subprocess.run(['lake','env','lean','--run','DiagnosticExt4Parity.lean',str(input_path),str(output_path)],cwd=root,check=True)
rows=json.loads(output_path.read_text());assert len(rows)==len(cases)
for (a,b),row in zip(cases,rows):
 expected=[list(add(a,b)),list(sub(a,b)),list(mul(a,b)),list(mul(a,b))]
 assert row==expected
report=dict(status='PASS',operand_pairs=len(cases),operation_comparisons=4*len(cases),sources={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [root/'DiagnosticExt4Parity.lean',root/'NearCompression/DiagnosticExt4Embedding.lean',Path(__file__).parent/'check_whir_handoff.py']},scope='Canonical operand executable parity, including all basis pairs, modular boundaries, and deterministic mixed coordinates. Complements universal algebra lemmas; not parser/native implementation or cryptographic security proof.')
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
