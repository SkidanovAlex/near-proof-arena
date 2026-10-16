"""Shared path parity vs independent individual paths; exhaustive small subsets."""
import itertools,json,random,copy,sys
from pathlib import Path
from pq384_primitives import merkle_tree,merkle_path,field_words
from pq384_multiproof import compress,expand
from pq384_source_cache import SourceCache
rng=random.Random(384);cases=0;rejected=0
for count in (2,4,8,32,128):
    leaves=[rng.randbytes(17+i%7) for i in range(count)];ctx=b'shared-path-test'
    root,layers=merkle_tree(leaves,ctx)
    sets=([i for i in range(count) if mask>>i&1] for mask in range(1,1<<count)) if count<=8 else ([rng.randrange(count) for _ in range(k)] for k in (1,8,40,150))
    for indices in sets:
        indices=indices+[indices[0]] # duplicate queries preserved
        selected=[leaves[i] for i in indices];paths=[merkle_path(layers,i) for i in indices]
        proof=compress(root,ctx,count,indices,selected,paths)
        assert expand(root,ctx,count,indices,proof)==(selected,paths);cases+=1
        bad=copy.deepcopy(proof);bad['leaves'][0]=b'changed'
        try:expand(root,ctx,count,indices,bad)
        except ValueError:rejected+=1
        else:raise AssertionError('changed leaf accepted')
        bad=copy.deepcopy(proof);bad['siblings'].append(bytes(48))
        try:expand(root,ctx,count,indices,bad)
        except ValueError:rejected+=1
        else:raise AssertionError('extra node accepted')
full=[]
if len(sys.argv)>1:
    info=json.loads(Path(sys.argv[1]).read_text())
    with SourceCache(info['cache_directory'],expected_root=bytes.fromhex(info['root_hex']),log_rows=13,width=544,packing=32) as cache:
        for queries in (8,335,445):
            indices=[rng.randrange(2*cache.degree) for _ in range(queries)]
            openings=[cache.opening(i) for i in indices]
            leaves=[field_words(q['leaf']) for q in openings];paths=[[bytes.fromhex(h) for h in q['path']] for q in openings]
            proof=compress(cache.root,cache.context,2*cache.degree,indices,leaves,paths)
            assert expand(cache.root,cache.context,2*cache.degree,indices,proof)==(leaves,paths)
            full.append(dict(queries=queries,individual_bytes=sum(map(len,leaves))+sum(len(p)*48 for p in paths),
                shared_bytes=sum(map(len,proof['leaves']))+48*len(proof['siblings']),unique_leaves=len(proof['leaves'])))
print(json.dumps(dict(status='PASS',small_cases=cases,negative_checks=rejected,fullheight=full,
    scope='Leaf+authentication payload only; exact expansion preserves individual queries. No security certification.'),indent=2))
