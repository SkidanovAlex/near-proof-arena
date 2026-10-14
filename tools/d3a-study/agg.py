import json, sys, os, collections, statistics as st
R=822756; G=(1<<22)*R
rows=[json.loads(l) for f in sys.argv[1:] for l in open(f)]
def fam(o):
    if o=='charge': return 'gas-charge(pseudo)'
    o=int(o)
    if o in (0x20,0x21,0x22): return 'local get/set/tee'
    if o in (0x41,0x42): return 'const'
    if 0x28<=o<=0x35: return 'load'
    if 0x36<=o<=0x3e: return 'store'
    if o in (0x23,0x24): return 'global'
    if o in (0x0c,0x0d,0x0e,0x04,0x05,0x0f,0x0b,0x00): return 'control(br/if/ret)'
    if o in (0x10,0x11): return 'call/call_indirect'
    if o in (0x6c,0x7e): return 'mul'
    if o in (0x6d,0x6e,0x6f,0x70,0x7f,0x80,0x81,0x82): return 'div/rem'
    if o in (0x71,0x72,0x73,0x83,0x84,0x85): return 'bitwise'
    if o in (0x74,0x75,0x76,0x77,0x78,0x86,0x87,0x88,0x89,0x8a): return 'shift/rot'
    if o in (0x6a,0x6b,0x7c,0x7d): return 'add/sub'
    if 0x45<=o<=0x5a: return 'compare/eqz'
    if o in (0x67,0x68,0x69,0x79,0x7a,0x7b): return 'clz/ctz/popcnt'
    if o in (0xa7,0xac,0xad,0xc0,0xc1,0xc2,0xc3,0xc4): return 'convert/extend'
    if o in (0x1a,0x1b,0x1c): return 'drop/select'
    if o>=0xfc00 or o in (0x3f,0x40): return 'bulk-mem/table/msize/grow'
    return 'other:%x'%o
acc=[r for r in rows if r['verdict'][0]=='accept']
print('cases',len(rows),'accepted',len(acc), 'verdicts',collections.Counter(r['verdict'][0] for r in rows))
F=collections.Counter(); H=collections.Counter(); HG=collections.Counter()
per=[]
for r in acc:
    ins=sum(v for k,v in r['ops'].items() if k!='charge'); ch=r['ops'].get('charge',0)
    for k,v in r['ops'].items(): F[fam(k)]+=v
    H.update(r['host']); HG.update(r['hostgas'])
    burnt=sum(c['burnt'] for c in r['calls'])
    per.append(dict(case=r['case'],ins=ins,ch=ch,host=sum(r['host'].values()),calls=len(r['calls']),
       pages=max([c['pages'] for c in r['calls']] or [0]), code=max([c['code_len'] for c in r['calls']] or [0]),
       burnt=burnt, opgas=r['charge_gas'], memio=sum(v for k,v in r['memio'].items() if k.endswith('bytes'))))
def q(xs,p):
    xs=sorted(xs); return xs[min(len(xs)-1,int(p*len(xs)))]
for k in ['ins','ch','host','calls','pages','code','burnt','opgas','memio']:
    xs=[p[k] for p in per]
    print(f"{k:6s} mean={st.mean(xs):.4g} p50={q(xs,.5):.4g} p90={q(xs,.9):.4g} p99={q(xs,.99):.4g} max={max(xs):.4g}")
tb=sum(p['burnt'] for p in per); to=sum(p['opgas'] for p in per)
print('aggregate: wasm-op (charge) gas share of FC burnt gas = %.3f'%(to/tb))
mx=max(per,key=lambda p:p['ins']); print('max-instr case',mx)
print('ins per Tgas burnt (aggregate) = %.4g'%(sum(p['ins'] for p in per)/(tb/1e12)))
heavy=[p for p in per if p['burnt']>G/10]
if heavy: print('cases burnt>0.1 G_alpha:',len(heavy),'ins/Tgas there = %.4g'%(sum(p['ins'] for p in heavy)/(sum(p['burnt'] for p in heavy)/1e12)), 'opgas share %.3f'%(sum(p['opgas'] for p in heavy)/sum(p['burnt'] for p in heavy)))
T=sum(F.values()); print('opcode families (share of executed flat-IR incl. charge pseudo-ops):')
for k,v in F.most_common(): print(f"  {k:28s} {v:12d} {100*v/T:6.2f}%")
print('host calls total',sum(H.values()),'distinct',len(H))
for k,v in H.most_common(25): print(f"  {k:40s} {v:8d}  gas {HG[k]/1e12:9.3f} Tgas")
print('host gas total %.3f Tgas of burnt %.3f'%(sum(HG.values())/1e12,tb/1e12))
