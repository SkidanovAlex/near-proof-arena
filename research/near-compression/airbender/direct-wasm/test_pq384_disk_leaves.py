"""End-to-end exact leaf/tree/root parity from existing coefficient caches."""
import argparse,json,tempfile,time,hashlib
from pathlib import Path
from pq384_disk_leaves import build_disk_leaves
from pq384_disk_tree import build_disk_tree
from pq384_native_fft import NativeFFT
from pq384_source_cache import SourceCache
from test_pq384_disk_tree import equal_files


def main():
    p=argparse.ArgumentParser();p.add_argument('--library',type=Path,required=True);p.add_argument('--cache',type=Path,action='append',required=True);p.add_argument('--report',type=Path,required=True);a=p.parse_args()
    native=NativeFFT(a.library);reports=[]
    with tempfile.TemporaryDirectory(prefix='near-disk-leaves-') as directory:
        for i,cache in enumerate(a.cache):
            m=json.loads((cache/'manifest.json').read_text());dest=Path(directory)/str(i);dest.mkdir()
            for name in ['manifest.json','coefficients.u32']:(dest/name).symlink_to((cache/name).resolve())
            start=time.monotonic()
            build_disk_leaves(cache/'coefficients.u32',dest/'leaves.u32',degree=m['degree'],lanes=m['lanes'],native=native,tile_leaves=257)
            leaf_seconds=time.monotonic()-start
            equal_files(cache/'leaves.u32',dest/'leaves.u32')
            root=build_disk_tree(dest/'leaves.u32',dest/'tree.sha384',leaf_count=m['leaf_count'],leaf_bytes=m['lanes']*8,context=bytes.fromhex(m['context_hex']))
            assert root.hex()==m['root_hex'];equal_files(cache/'tree.sha384',dest/'tree.sha384')
            args=dict(expected_root=root,log_rows=m['rows'].bit_length()-1,width=m['width'],packing=m['packing'])
            with SourceCache(cache,**args) as old,SourceCache(dest,**args) as new:
                for index in sorted(set([0,1,m['leaf_count']//2,m['leaf_count']-1])):assert old.opening(index)==new.opening(index)
            reports.append(dict(cache=str(cache),degree=m['degree'],lanes=m['lanes'],leaf_seconds=leaf_seconds,leaf_bytes=(dest/'leaves.u32').stat().st_size,exact_leaves_tree_root_and_openings=True,tile_leaves=257,scope='No RSS measurement; existing coefficients remain an input.'))
    a.report.write_text(json.dumps(dict(status='PASS',library_sha256=hashlib.sha256(a.library.read_bytes()).hexdigest(),cases=reports),indent=2)+'\n')

if __name__=='__main__':main()
