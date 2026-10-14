import json, os, sys, glob, statistics as st
G_ALPHA = (1<<22)*822756
roots = sys.argv[1:]
rows=[]
for r in roots:
    for d in sorted(glob.glob(os.path.join(r,'*'))):
        mp=os.path.join(d,'meta.json')
        if not os.path.exists(mp): continue
        m=json.load(open(mp))
        f=m.get('features',{})
        if 'fc_gas_burnt_for_function_call' not in f: continue
        rows.append(dict(case=d, in_d3=m.get('in_d3'), rel=m.get('expected_rel_d3'),
          fcg=int(f.get('fc_gas_burnt_for_function_call',0)), fcb=int(f.get('fc_gas_burnt',0)),
          nfc=f.get('n_function_calls',0), code_bytes=f.get('code_bytes',0), code_blobs=f.get('code_blobs',0),
          nprom=f.get('n_promises',0), nrc=f.get('n_receipts',0), logs=f.get('n_logs',0), wb=f.get('witness_bytes',0),
          cls=m.get('workload_class'), codes=[(c.get('name'),c.get('len')) for c in m.get('codes',[])],
          viol=m.get('d3_violations',[])))
def q(xs,p): 
    xs=sorted(xs); return xs[min(len(xs)-1,int(p*len(xs)))] if xs else None
ind=[r for r in rows if r['in_d3']]
print('cases with fc meta',len(rows),'in_d3',len(ind))
for k in ['fcg','nfc','code_bytes','code_blobs','nprom','nrc','logs','wb']:
    xs=[r[k] for r in ind]
    print(f"{k:12s} mean={st.mean(xs):.4g} p50={q(xs,.5)} p90={q(xs,.9)} p99={q(xs,.99)} max={max(xs)}")
xs=[r['fcg'] for r in ind]
print('max fcg / G_alpha =', max(xs)/G_ALPHA, ' cases >0.5 G_alpha:', sum(x>G_ALPHA/2 for x in xs), '>0.1:', sum(x>G_ALPHA/10 for x in xs))
oodg=[r for r in rows if 'e.g_alpha' in ' '.join(r['viol'])]
print('ood g_alpha cases', len(oodg), 'their fcg max/G', max([r['fcg'] for r in oodg],default=0)/G_ALPHA)
names={}
for r in ind:
    for n,l in r['codes']: names[n]=l
print('contracts', names)
from collections import Counter
print(Counter(r['cls'] for r in ind).most_common())
top=sorted(ind,key=lambda r:-r['fcg'])[:15]
for r in top: print(r['fcg']/1e12, r['nfc'], r['case'])
json.dump(rows, open('metascan-'+os.path.basename(roots[0].rstrip('/').split('/')[-2] if 'corpora' in roots[0] else 'pub')+'.json','w'))
