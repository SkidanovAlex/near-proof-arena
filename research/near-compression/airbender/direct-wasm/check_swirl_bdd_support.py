"""Exact finite Boolean support check, independent of BDD construction.

Containment plus exact accepted-assignment count checks the entire Boolean cube
without enumerating it. This Python checker is not yet refined in Lean.
"""
import functools,hashlib,json
from pathlib import Path
from prove_swirl_root_public_dag import context,OUT as GKR
from swirl_wiring_bdd import build,variable_order


def check_support(nodes,root,keys,order):
    n=len(order)
    if sorted(order)!=list(range(n)):raise ValueError('variable permutation')
    if len(nodes)<2 or nodes[:2]!=[None,None]:raise ValueError('terminals')
    if type(root)is not int or not 0<=root<len(nodes):raise ValueError('root')
    keys=list(keys)
    if len(set(keys))!=len(keys) or any(type(k)is not int or not 0<=k<1<<n for k in keys):
        raise ValueError('support shape')
    rank={bit:i for i,bit in enumerate(order)}
    for i,node in enumerate(nodes[2:],2):
        if len(node)!=3:raise ValueError('node shape')
        bit,lo,hi=node
        if bit not in rank or any(type(j)is not int or not 0<=j<i for j in (lo,hi)):
            raise ValueError('acyclic ordered node')
        if any(j>1 and rank[nodes[j][0]]<=rank[bit] for j in (lo,hi)):
            raise ValueError('repeated or backwards variable')
    @functools.lru_cache(None)
    def count(i,level):
        if i==0:return 0
        if i==1:return 1<<(n-level)
        bit,lo,hi=nodes[i];j=rank[bit]
        if j<level:raise ValueError('level')
        return (1<<(j-level))*(count(lo,j+1)+count(hi,j+1))
    accepted=count(root,0)
    if accepted!=len(keys):raise ValueError('support cardinality')
    for k in keys:
        i=root
        while i>1:
            bit,lo,hi=nodes[i];i=hi if (k>>bit)&1 else lo
        if i!=1:raise ValueError('missing support element')
    return accepted


def main():
    layout,*_=context();records=[];negatives=0
    for layer,gates in enumerate(layout['layers']):
        n=(len(gates)-1).bit_length()
        prev=layout['input_size'] if layer==0 else len(layout['layers'][layer-1])
        m=(prev-1).bit_length();order=variable_order(n,m,'interleaved_012_high')
        for op in ('add','sub','mul'):
            keys=[k+(i<<n)+(j<<(n+m)) for k,(tag,i,j) in enumerate(gates) if tag==op]
            nodes,root=build(keys,order)
            assert check_support(nodes,root,keys,order)==len(keys)
            # Empty/full substitution, deletion, extra expected point, and bad order.
            mutations=[(nodes,1 if not keys else 0,keys,order)]
            if keys:mutations.append((nodes,root,keys[1:],order))
            keyset=set(keys)
            extra=next((x for x in range(len(keys)+1) if x not in keyset),None)
            if extra is not None and extra<1<<len(order):
                mutations.append((nodes,root,keys+[extra],order))
                if keys:mutations.append((nodes,root,[extra]+keys[1:],order))
            if order:mutations.append((nodes+[(order[0],len(nodes),0)],len(nodes),keys,order))
            if len(order)>1:mutations.append((nodes,root,keys,[order[0]]*len(order)))
            for args in mutations:
                try:check_support(*args)
                except ValueError:negatives+=1
                else:raise AssertionError('mutation accepted')
            records.append(dict(layer=layer,op=op,variables=len(order),nodes=len(nodes),support=len(keys),
                graph_sha256=hashlib.sha256(json.dumps([nodes,root,order],separators=(',',':')).encode()).hexdigest()))
    out=GKR.parent/'bdd-support';out.mkdir(exist_ok=True)
    report=dict(status='EXACT_BOOLEAN_SUPPORT_CHECKED',graphs=len(records),support_elements=sum(x['support'] for x in records),
        rejected=negatives,records=records,limitations=['Python structural/count checker not formally refined.',
            'Lean theorem applies to ordered unfolded view; explicit graph-to-view bridge remains.',
            'No transcript, PCS, PQ128 or full NEAR claim.'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print({k:v for k,v in report.items() if k!='records'})


if __name__=='__main__':main()
