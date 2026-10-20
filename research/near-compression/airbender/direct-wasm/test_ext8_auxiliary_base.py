"""Differential generator checks; does not change the running prover."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import random
import time
import pq384_ext8_auxiliary_base as fast
import pq384_ext8_auxiliary as ref
import pq384_ext8_reference as f

ROOT=Path(__file__).resolve().parents[2]


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();rng=random.Random(846084)
    scalar=lambda:tuple(rng.randrange(f.P) for _ in range(8))
    cases=[]
    table=dict(width=3,interactions=[
        dict(bus=0,send=True,mult=[],msg=[]),
        dict(bus=3,send=False,mult=[['v',0,0]],msg=[['+', ['v',1,1], ['p',9]],['trans']]),
        dict(bus=1,send=True,mult=[['v',0,0],['c',2],['last']],msg=[['*',['v',1,0],['-', ['v',2,1]]],['first'],['p',0]])])
    for n in (2,4,8):
        rows=[[rng.randrange(f.P) for _ in range(3)] for _ in range(n)]
        cases.append((table,rows,[19],scalar(),scalar()))
    cases.append((dict(width=1,interactions=[dict(bus=0,send=True,mult=[['c',1],['c',1]],msg=[])]),[[0],[0]],[],f.ZERO,f.ONE))
    capture=ROOT/'results/sha384-nibble64';st=json.loads(gzip.decompress((capture/'statement.json.gz').read_bytes()))
    for i,t in enumerate(st['spec']['air']['tables']):
        rows=json.loads(gzip.decompress((capture/f'source-{i:02d}-rows.json.gz').read_bytes()))['rows'][:2]
        cases.append((t,rows,[],scalar(),scalar()))
    round_rows=json.loads(gzip.decompress((capture/'source-01-rows.json.gz').read_bytes()))['rows'][:512]
    cases.append((st['spec']['air']['tables'][1],round_rows,[],scalar(),scalar()))
    old_seconds=new_seconds=0;cells=0;timings=[]
    for t,rows,pub,alpha,gamma in cases:
        start=time.monotonic();old=ref.generate(t,rows,pub,alpha,gamma);old_time=time.monotonic()-start;old_seconds+=old_time
        start=time.monotonic();new=fast.generate(t,rows,pub,alpha,gamma);new_time=time.monotonic()-start;new_seconds+=new_time
        timings.append(dict(rows=len(rows),reference_seconds=old_time,base_evaluation_seconds=new_time))
        assert old==new
        cells+=sum(len(row)*8 for row in new['aux_rows'])
    sources=[Path(__file__),Path(fast.__file__),Path(ref.__file__),Path(f.__file__),Path(fast.expr_degree.__code__.co_filename)]
    report=dict(status='EXACT_AUXILIARY_GENERATOR_PARITY',cases=len(cases),auxiliary_base_cells_compared=cells,
        reference_seconds=old_seconds,base_evaluation_seconds=new_seconds,large_case=timings[-1],
        scope='Exact parity for synthetic nonboolean multiplicities, next/public/selector expressions, empty messages/multiplicities, zero factors, two source rows of all11retained tables, and512retained round rows. Not full-trace equivalence, a Lean refinement, or a changed verifier. Timing is this bounded CPU test only.',
        input_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [capture/'statement.json.gz']+[capture/f'source-{i:02d}-rows.json.gz' for i in range(11)]},
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
