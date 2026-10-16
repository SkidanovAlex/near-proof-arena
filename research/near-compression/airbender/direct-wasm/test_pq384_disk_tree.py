"""Independent reference parity and real source-cache byte-for-byte parity."""
import argparse,json,tempfile,tracemalloc,time
from pathlib import Path
from pq384_disk_tree import build_disk_tree
from pq384_primitives import merkle_tree
from pq384_source_cache import SourceCache


def equal_files(a,b):
    with a.open('rb') as left,b.open('rb') as right:
        while True:
            x=left.read(65536);y=right.read(65536)
            assert x==y
            if not x:return


def main():
    p=argparse.ArgumentParser();p.add_argument('--cache',type=Path,action='append',default=[]);p.add_argument('--report',type=Path,required=True);a=p.parse_args()
    results=[]
    with tempfile.TemporaryDirectory(prefix='near-disk-tree-') as directory:
        work=Path(directory)
        for power in range(1,9):
            leaves=[bytes((i+j)%256 for j in range(13)) for i in range(1<<power)]
            src=work/f'small-{power}.leaves';dst=work/f'small-{power}.tree';src.write_bytes(b''.join(leaves))
            root,layers=merkle_tree(leaves,b'independent-reference')
            assert build_disk_tree(src,dst,leaf_count=len(leaves),leaf_bytes=13,context=b'independent-reference')==root
            assert dst.read_bytes()==b''.join(v for layer in layers for v in layer)
            try:build_disk_tree(src,dst,leaf_count=len(leaves),leaf_bytes=13,context=b'independent-reference')
            except FileExistsError:pass
            else:raise AssertionError('overwrote prior tree')
        for i,cache in enumerate(a.cache):
            m=json.loads((cache/'manifest.json').read_text());dest=work/f'cache-{i}';dest.mkdir()
            for name in ['manifest.json','leaves.u32','coefficients.u32']:(dest/name).symlink_to((cache/name).resolve())
            tracemalloc.start();start=time.monotonic()
            root=build_disk_tree(cache/'leaves.u32',dest/'tree.sha384',leaf_count=m['leaf_count'],leaf_bytes=m['lanes']*8,context=bytes.fromhex(m['context_hex']))
            elapsed=time.monotonic()-start;_,peak=tracemalloc.get_traced_memory();tracemalloc.stop()
            assert root.hex()==m['root_hex'];equal_files(cache/'tree.sha384',dest/'tree.sha384')
            args=dict(expected_root=root,log_rows=m['rows'].bit_length()-1,width=m['width'],packing=m['packing'])
            with SourceCache(cache,**args) as old,SourceCache(dest,**args) as new:
                for index in sorted(set([0,1,m['leaf_count']//2,m['leaf_count']-1])):assert old.opening(index)==new.opening(index)
            results.append(dict(cache=str(cache),leaf_count=m['leaf_count'],tree_bytes=(dest/'tree.sha384').stat().st_size,seconds=elapsed,python_traced_peak_bytes=peak,exact_tree_and_root=True,authenticated_opening_parity=True))
    a.report.write_text(json.dumps(dict(status='PASS',small_reference_cases=8,actual_caches=results,scope='Tree construction only; leaves and coefficients already exist. Python-traced allocations are not RSS or total prover memory.'),indent=2)+'\n')

if __name__=='__main__':main()
