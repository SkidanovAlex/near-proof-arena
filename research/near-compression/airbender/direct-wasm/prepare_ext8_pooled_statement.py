"""Prepare source-bank roots from fixture rows before execution challenges.
The use root and logical spec remain fixed by the supplied template/receipt.
This does not turn a fixture into an externally anchored NEAR state statement.
"""
import argparse,gzip,hashlib,json,subprocess,tempfile,time
from pathlib import Path
import ext8_commitment_profiles as cp
from pq384_ext8_native import Kernel
from verify_sha384_node_chunk import contract


def main():
    p=argparse.ArgumentParser()
    for key in ('template','receipt','source-directory','output','report'):p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args();start=time.perf_counter()
    template=json.loads(a.template.read_text());receipt=json.loads(a.receipt.read_text());contract(template,receipt)
    expected=json.loads(gzip.decompress(Path('results/ext8-affine-q309/prover-report.json.gz').read_bytes()))['source_sha256']
    rows=[]
    for i,digest in enumerate(expected):
        raw=(a.source_directory/f'source-{i:02d}-rows.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==digest
        rows.append(json.loads(raw)['rows'])
    print('Loaded original fixture rows; committing physical source banks',flush=True)
    source=Path(__file__).with_name('native-folded')/'kernel_ext8.rs'
    with tempfile.TemporaryDirectory(prefix='pooled-prepare-') as tmp:
        lib=Path(tmp)/'kernel.so';subprocess.run(['rustc','--edition=2024','--crate-type','cdylib','-O',str(source),'-o',str(lib)],check=True)
        caches=cp.source_caches(template['spec'],rows,Kernel(lib))
    roots=[c.root.hex() for c in caches];assert roots[3]==template['roots'][3]
    statement=dict(spec=template['spec'],roots=roots);cp.check_roots(statement['spec'],roots,profile='phase-pooled-v1');contract(statement,receipt)
    a.output.write_text(json.dumps(statement,separators=(',',':'))+'\n')
    report=dict(status='PASS',source_sha256=expected,use_root_unchanged=True,logical_spec_unchanged=True,roots=roots,
                banks=cp.plan(statement['spec']),seconds=time.perf_counter()-start,
                statement_sha256=hashlib.sha256(a.output.read_bytes()).hexdigest(),
                scope='Fixture source commitments prepared before bus/local challenges. No auxiliary root chosen here and no full NEAR/PQ claim.')
    a.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
