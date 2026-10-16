"""Externally selected execution commitment geometry; never proof-selected.
Phase-pooled-v1 fixes three physical banks while preserving four logical AIR
source slots. Logical source roots0/1/2 alias; all auxiliary roots alias.
"""
import json
import ext8_pooled_weights as pool
import pq384_ext8_weight_families as families
from pq384_primitives import require,hash_parts
PROFILES=('separate','phase-pooled-v1')


def plan(spec):
    require(len(spec['air']['tables'])==len(spec['log_rows'])==4,'pooled four-table profile')
    banks=pool.phase_layout(spec,3)
    require(len(banks)==3 and [b['phase'] for b in banks]==['source','auxiliary','source'],'pooled bank phases')
    for bank,packing in zip(banks,(128,32,spec['source_packings'][3])):
        require(type(packing)is int and packing>0 and packing&(packing-1)==0,'pooled packing')
        bank['packing']=packing
        require(((1<<bank['log_rows'])*packing)<=262144 and (bank['width']+packing-1)//packing<=64,'pooled bank capacity')
    return banks


def check_roots(spec,roots,aux_roots=None,profile='separate'):
    require(profile in PROFILES,'commitment profile')
    if profile=='separate':return
    plan(spec)
    require(len(roots)==4 and roots[0]==roots[1]==roots[2],'pooled source root aliases')
    if aux_roots is not None:
        require(len(aux_roots)==4 and all(r==aux_roots[0] for r in aux_roots),'pooled auxiliary root aliases')


def statement(spec,roots,profile='separate'):
    check_roots(spec,roots,profile=profile)
    domain=(b'ext8-execution-reduction-diagnostic-v1' if profile=='separate' else b'ext8-execution-phase-pooled-diagnostic-v1')
    return hash_parts(domain,json.dumps(spec,sort_keys=True).encode(),*roots)


def bank_rows(bank,rows):
    output=[[0]*bank['width'] for _ in range(1<<bank['log_rows'])]
    for block in bank['blocks']:
        source=rows[block['table']];offset=block['offset'];width=block['width']
        require(len(source)==1<<block['log_rows'] and all(len(row)==width for row in source),'logical source shape')
        for i,row in enumerate(source):output[i][offset:offset+width]=row
    return output


def source_caches(spec,rows,native):
    import pq384_ext8_weighted as pcs
    banks=plan(spec)
    first=pcs.Source(bank_rows(banks[0],rows),banks[0]['packing'],native)
    use=pcs.Source(bank_rows(banks[2],rows),banks[2]['packing'],native)
    return [first,first,first,use]


def auxiliary_caches(spec,rows,native):
    import pq384_ext8_weighted as pcs
    bank=plan(spec)[1];cache=pcs.Source(bank_rows(bank,rows),bank['packing'],native)
    return [cache]*4


def bind_branches(spec,descriptors,roots,aux_roots,profile='separate'):
    check_roots(spec,roots,aux_roots,profile)
    if profile=='separate':
        return [{**{k:v for k,v in b.items() if k not in ('table','branch')},
                 'root':(roots if b['branch']==0 else aux_roots)[b['table']]} for b in descriptors]
    banks=plan(spec);logical={}
    for b in descriptors:
        require(set(b)=={'table','branch','log_rows','width','packing','row_point','lanes'},'logical descriptor fields')
        key=(b['table'],b['branch']);require(key not in logical,'duplicate logical descriptor');logical[key]=b
    expected={(block['table'],int(bank['phase']=='auxiliary')) for bank in banks for block in bank['blocks']}
    require(set(logical)==expected,'logical descriptor coverage')
    result=[]
    for bank in banks:
        kind=int(bank['phase']=='auxiliary');terms=[]
        for block in bank['blocks']:
            b=logical[block['table'],kind]
            require((b['log_rows'],b['width'],b['packing'])==(block['log_rows'],block['width'],spec['aux_packings' if kind else 'source_packings'][block['table']]),'logical descriptor geometry')
            families.validate_weights(b)
            terms.append(dict(offset=block['offset'],width=block['width'],row_point=b['row_point'],
                current=[x for lane in b['lanes'] for x in lane[0]][:block['width']],
                next=[x for lane in b['lanes'] for x in lane[1]][:block['width']]))
        root=(aux_roots if kind else roots)[bank['blocks'][0]['table']]
        if bank is banks[2]:
            b=logical[3,0];result.append({**{k:v for k,v in b.items() if k not in ('table','branch')},'root':root})
        else:result.append(dict(root=root,log_rows=bank['log_rows'],width=bank['width'],packing=bank['packing'],terms=terms))
    return result


def opening_caches(sources,auxiliaries,descriptors,profile='separate'):
    require(profile in PROFILES,'commitment profile')
    if profile=='phase-pooled-v1':return [sources[0],auxiliaries[0],sources[3]]
    return [(sources if b['branch']==0 else auxiliaries)[b['table']] for b in descriptors]
