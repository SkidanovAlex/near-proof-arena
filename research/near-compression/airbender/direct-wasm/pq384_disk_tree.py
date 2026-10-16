"""Prover-only Merkle builder with disk-backed layers and bounded live buffers.

Preserves source-cache tree.sha384 bytes. Input leaves must remain immutable
throughout the call. No commitment security or native-memory proof is claimed.
"""
from pathlib import Path
from pq384_primitives import hash_parts,u64,require


def build_disk_tree(leaves_path,tree_path,*,leaf_count,leaf_bytes,context):
    require(type(leaf_count) is int and leaf_count>=2 and leaf_count&(leaf_count-1)==0,'leaf count')
    require(type(leaf_bytes) is int and leaf_bytes>0,'leaf width')
    require(type(context) is bytes,'context')
    with Path(leaves_path).open('rb') as leaves:
        require(leaves.seek(0,2)==leaf_count*leaf_bytes,'leaf file size');leaves.seek(0)
        # Exclusive creation protects prior caches and allows a read handle on
        # the same file after flushing each complete layer.
        with Path(tree_path).open('xb') as output:
            for i in range(leaf_count):
                leaf=leaves.read(leaf_bytes)
                require(len(leaf)==leaf_bytes,'truncated leaf')
                output.write(hash_parts(b'merkle/leaf',context,u64(i),leaf))
            output.flush()
            offset=0;count=leaf_count;level=1
            with Path(tree_path).open('rb') as previous:
                while count>1:
                    previous.seek(offset)
                    for _ in range(count//2):
                        pair=previous.read(96)
                        require(len(pair)==96,'truncated tree layer')
                        output.write(hash_parts(b'merkle/node',context,u64(level),pair[:48],pair[48:]))
                    output.flush()
                    offset+=count*48;count//=2;level+=1
                previous.seek(offset);top=previous.read(48)
                require(len(top)==48,'missing root')
            return hash_parts(b'merkle/root',context,u64(leaf_count),top)
