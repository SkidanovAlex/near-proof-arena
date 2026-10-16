"""Canonical shared Merkle paths using unchanged SHA384 tree semantics.

Indices/count/context/root are verifier inputs. Duplicate queries share bytes
but remain duplicate verifier queries; no sampling or security bound changes.
"""
from pq384_primitives import require,hash_parts,u64,verify_path

def shape(count,indices):
    require(type(count)is int and 2<=count<=1<<26 and count&(count-1)==0,'multiproof count')
    require(isinstance(indices,list) and 0<len(indices)<=1<<20 and
            all(type(i)is int and 0<=i<count for i in indices),'multiproof indices')
    return sorted(set(indices))

def boundary(count,indices):
    active=shape(count,indices);result=[]
    for level in range(count.bit_length()-1):
        known=set(active)
        result.extend((level,i^1) for i in active if i^1 not in known)
        active=sorted({i//2 for i in active})
    return result

def compress(expected_root,context,count,indices,leaves,paths):
    unique=shape(count,indices)
    require(isinstance(leaves,list) and isinstance(paths,list) and len(leaves)==len(paths)==len(indices),'multiproof inputs')
    leafmap={};nodes={}
    for i,leaf,path in zip(indices,leaves,paths):
        verify_path(expected_root,context,count,i,leaf,path)
        require(i not in leafmap or leafmap[i]==leaf,'duplicate leaf disagreement');leafmap[i]=leaf
        for level,h in enumerate(path):
            key=(level,(i>>level)^1)
            require(key not in nodes or nodes[key]==h,'shared node disagreement');nodes[key]=h
    return {'leaves':[leafmap[i] for i in unique],
            'siblings':[nodes[key] for key in boundary(count,indices)]}

def expand(expected_root,context,count,indices,proof):
    unique=shape(count,indices);needed=boundary(count,indices)
    require(type(context)is bytes and type(expected_root)is bytes and len(expected_root)==48,'multiproof context/root')
    require(type(proof)is dict and set(proof)=={'leaves','siblings'},'multiproof fields')
    leaves=proof['leaves'];siblings=proof['siblings']
    require(isinstance(leaves,list) and len(leaves)==len(unique) and all(type(v)is bytes for v in leaves),'multiproof leaves')
    require(isinstance(siblings,list) and len(siblings)==len(needed) and
            all(type(v)is bytes and len(v)==48 for v in siblings),'multiproof siblings')
    nodes=dict(zip(needed,siblings));leafmap=dict(zip(unique,leaves))
    for i in unique:nodes[(0,i)]=hash_parts(b'merkle/leaf',context,u64(i),leafmap[i])
    active=unique
    for level in range(count.bit_length()-1):
        parents=sorted({i//2 for i in active})
        for p in parents:
            nodes[(level+1,p)]=hash_parts(b'merkle/node',context,u64(level+1),nodes[(level,2*p)],nodes[(level,2*p+1)])
        active=parents
    top=nodes[(count.bit_length()-1,0)]
    require(hash_parts(b'merkle/root',context,u64(count),top)==expected_root,'multiproof root mismatch')
    return ([leafmap[i] for i in indices],
            [[nodes[(level,(i>>level)^1)] for level in range(count.bit_length()-1)] for i in indices])
