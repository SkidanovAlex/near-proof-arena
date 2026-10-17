"""Read-only captured-transcript metadata/parity audit; no security claim.
Reference modules are loaded from --reference-dir; outputs go only to --output.
"""
import argparse,copy,hashlib,json,sys,time
from pathlib import Path

def check(ok,label):
    if not ok: raise ValueError(label)

def log2(n):
    check(type(n)is int and n>0 and n&(n-1)==0,'power of two');return n.bit_length()-1

def expected_metadata(spec,circuit,layout):
    widths=[t['width']+4*bus.aux.layout(t)['aux_columns'] for t in spec['air']['tables']]
    offset=0;blocks={}
    for ti in sorted(range(len(widths)),key=lambda i:(-(1<<(widths[i]-1).bit_length()),i)):
        W=1<<(widths[ti]-1).bit_length();blocks[ti]=dict(table=ti,offset=offset,column_capacity=W,block_size=2*W);offset+=2*W
    check(circuit['input_blocks']==list(blocks.values()),'compiler block placement')
    capacity=1<<(offset-1).bit_length()
    check(capacity==circuit['private_input_capacity']==layout['private_capacity'],'private capacity')
    R=sum(spec['log_rows']);m=log2(layout['input_size']);lanes=[];certificates=[];row_offset=0;branch_index=0
    for ti,t in enumerate(spec['air']['tables']):
        sw=t['width'];aw=widths[ti]-sw;block=blocks[ti]
        certificates.append(dict(rowLog=spec['log_rows'][ti],rowOffset=row_offset,blockOffset=block['offset'],columnCapacity=block['column_capacity'],sourceWidth=sw,auxiliaryWidth=aw,sourcePackingLog=log2(spec['source_packings'][ti]),auxiliaryPackingLog=log2(spec['aux_packings'][ti]) if aw else 0))
        for kind,width,start,key in [('source',sw,0,'source_packings'),('aux',aw,sw,'aux_packings')]:
            if not width:continue
            p=log2(spec[key][ti])
            for group in range((width+(1<<p)-1)//(1<<p)):
                lanes.append(dict(table=ti,branch=kind,branch_index=branch_index,rowLog=spec['log_rows'][ti],packingLog=p,
                    rowOffset=row_offset,inputStart=block['offset']+start,nextOffset=block['column_capacity'],width=width,group=group))
            branch_index+=1
        row_offset+=spec['log_rows'][ti]
    C=max(e['rowLog']+e['packingLog'] for e in lanes)
    return dict(layout=dict(rowCoordinates=R,inputLog=m,commonLog=C,privateCapacity=capacity),tables=certificates,lanes=lanes)

def validate_metadata(meta,spec,circuit,layout):
    check(meta==expected_metadata(spec,circuit,layout),'canonical metadata mismatch')
    l=meta['layout'];check(l['privateCapacity']<=1<<l['inputLog'],'input envelope')
    for t in meta['tables']:
        check(t['rowOffset']+t['rowLog']<=l['rowCoordinates'],'certificate row bound')
        check(t['rowLog']+t['sourcePackingLog']<=l['commonLog'],'certificate source degree')
        check(t['auxiliaryWidth']==0 or t['rowLog']+t['auxiliaryPackingLog']<=l['commonLog'],'certificate aux degree')
        check(t['sourceWidth']+t['auxiliaryWidth']<=t['columnCapacity'],'certificate column capacity')
        check(t['blockOffset']+2*t['columnCapacity']<=l['privateCapacity'],'certificate block bound')
    for e in meta['lanes']:
        check(all(type(e[k])is int and e[k]>=0 for k in ('rowLog','packingLog','rowOffset','inputStart','nextOffset','width','group','table','branch_index')),'natural metadata')
        check(e['rowOffset']+e['rowLog']<=l['rowCoordinates'],'row bound')
        check(e['rowLog']+e['packingLog']<=l['commonLog'],'local degree bound')
        check(e['inputStart']+e['width']<=l['privateCapacity'],'current bound')
        check(e['inputStart']+e['nextOffset']+e['width']<=l['privateCapacity'],'next bound')
        check(e['group']*(1<<e['packingLog'])<e['width'],'nonempty lane')
    return True

def eq_at(point,index):
    ans=ONE
    for i,r in enumerate(point):ans=mul(ans,r if (index>>i)&1 else sub(ONE,r))
    return ans

def sum_ext(xs):
    ans=ZERO
    for x in xs:ans=add(ans,x)
    return ans

def zeta_slot(values,k):return sum_ext(v for c,v in enumerate(values) if c&k==k)

def column_mle(values,u):
    # Independent explicit upper-set sum and Boolean equality interpolation.
    return sum_ext(mul(zeta_slot(values,k),eq_at(u,k)) for k in range(len(values)))

def row_parts(point,u):
    cur=ONE
    for r,v in zip(point,u):cur=mul(cur,add(sub(ONE,v),mul(v,r)))
    # Cyclic predecessor enumeration, independent of optimized borrow DP.
    N=1<<len(point);eq=[eq_at(point,k) for k in range(N)];ans=ZERO
    for y in range(N):
        weight=ONE
        for i,v in enumerate(u):
            if not (y>>i)&1:weight=mul(weight,sub(ONE,v))
        ans=add(ans,mul(eq[(y-1)%N],weight))
    return cur,ans

def replay(directory):
    global bus
    statement=json.loads((directory/'statement.json').read_text());proof=json.loads((directory/'proof.json').read_text());spec=statement['spec'];roots=[bytes.fromhex(x) for x in statement['roots']]
    if proof['profile']=='near-pq384-seed-gkr-bus-v1':
        import pq384_seed_gkr_bus as bus
        st,t,a,g=bus.begin(spec,roots,bus.configure(spec['air']))
    else:
        check(proof['profile']=='near-pq384-gkr-bus-v1','captured profile')
        import pq384_gkr_bus as bus
        st,t,a,g=bus.begin(spec,roots)
    ars=[bus.pcs.decode_hash(x) for x in proof['aux_roots']];bus.initialize_aux(t,spec,ars,proof['finals'])
    terminals=[bus.constraint_verify(spec,t,ti,rounds) for ti,rounds in enumerate(proof['tables'])]
    circuit,layout,binding=bus.terminal_layout(spec,t,a,g,proof['finals'],terminals)
    ob=bus.gkr.verify(layout,binding,proof['gkr'])
    branches=bus.opening_arguments(spec,roots,ars,terminals,circuit,ob)
    parent=bus.opening_parent(binding,ob['transcript_seed'] if 'transcript_seed'in ob else proof['gkr'])
    degrees,D,contexts,pt,claim=bus.pcs.public(st,parent,branches,ob['private_claim']);u=[]
    for wire in proof['opening']['reduction']:
        r,_,claim=bus.pcs.round_start(pt,wire,claim);u.append(r)
    beta_ref=derived.betas(branches,degrees,D,u)
    check(beta_ref==bus.pcs.betas(branches,degrees,D,u),'derived/old beta parity')
    return spec,proof,terminals,circuit,layout,ob,branches,u,beta_ref

def run(directory,out):
    started=time.perf_counter();spec,proof,terminals,circuit,layout,ob,branches,u,beta_ref=replay(directory)
    meta=expected_metadata(spec,circuit,layout);validate_metadata(meta,spec,circuit,layout)
    l=meta['layout'];left,right=ob['queries'][0][0],ob['queries'][1][0];gamma=ob['queries'][1][1]
    check(ob['queries'][0][1]==ONE,'first GKR coefficient');check(len(left)==len(right)==l['inputLog'],'fixed captured input dimension')
    joined=[x for t in terminals for x in t['point']]+left+right+[gamma]+u
    check(len(joined)==l['rowCoordinates']+2*l['inputLog']+1+l['commonLog'],'joint coordinate count')
    private=[add(eq_at(left,i),mul(gamma,eq_at(right,i))) for i in range(l['privateCapacity'])]
    check(private==ob['private_weights'],'explicit eq private weights')
    counts=dict(lanes=0,slot_values=0,beta_values=0,lane_weight_positions=0,partial_lanes=0,negative_checks=0,row_pairs=0)
    cache={};selected=set()
    for e in meta['lanes']:
        n=e['rowLog'];p=e['packingLog'];pack=1<<p;row=joined[e['rowOffset']:e['rowOffset']+n];low=l['commonLog']-n-p;localu=joined[l['rowCoordinates']+2*l['inputLog']+1+low:];check(len(localu)==n+p,'PCS drop')
        columns=[]
        for side in (0,1):
            cols=[]
            for col in range(pack):
                c=e['group']*pack+col;slot=e['inputStart']+side*e['nextOffset']+c
                cols.append(add(eq_at(left,slot),mul(gamma,eq_at(right,slot))) if c<e['width'] else ZERO)
            columns.append(cols)
        actual=branches[e['branch_index']]['lanes'][e['group']]
        check(columns==[list(actual[0]),list(actual[1])],'branch_lanes exact lookup');counts['slot_values']+=2*pack
        key=(tuple(map(tuple,row)),tuple(map(tuple,localu[:n])))
        if key not in cache:cache[key]=row_parts(row,localu[:n]);counts['row_pairs']+=1
        a,b=cache[key];value=add(mul(a,column_mle(columns[0],localu[n:])),mul(b,column_mle(columns[1],localu[n:])))
        check(value==beta_ref[e['branch_index']][e['group']],'independent heterogeneous beta')
        check(value==weights.lane_weight_mle(row,*columns,localu),'actual lane_weight_mle');counts['beta_values']+=1
        if e['group']*pack+pack>e['width']:counts['partial_lanes']+=1
        # Run actual full lane_weights once per branch, inspect boundary/interior slots.
        if e['branch_index'] not in selected:
            selected.add(e['branch_index']);v=weights.lane_weights(row,*columns);N=1<<n
            for index in sorted({0,len(v)//2,len(v)-1}):
                col,k=divmod(index,N)
                rw=sum_ext(eq_at(row,y) for y in range(N) if y&k==k)
                nw=sum_ext(eq_at(row,(y-1)%N) for y in range(N) if y&k==k)
                expect=add(mul(zeta_slot(columns[0],col),rw),mul(zeta_slot(columns[1],col),nw))
                check(v[index]==expect,'actual lane_weights selected coefficient');counts['lane_weight_positions']+=1
        counts['lanes']+=1
    for field in ('rowLog','packingLog','rowOffset','inputStart','nextOffset','width','group','table','branch_index'):
        bad=copy.deepcopy(meta);bad['lanes'][0][field]+=1
        try:validate_metadata(bad,spec,circuit,layout)
        except ValueError:counts['negative_checks']+=1
        else:raise AssertionError('accepted changed '+field)
    for mutate in (lambda x:x['lanes'].pop(),lambda x:x['lanes'].reverse(),lambda x:x['lanes'].append(copy.deepcopy(x['lanes'][0])),lambda x:x['layout'].__setitem__('inputLog',x['layout']['inputLog']+1)):
        bad=copy.deepcopy(meta);mutate(bad)
        try:validate_metadata(bad,spec,circuit,layout)
        except ValueError:counts['negative_checks']+=1
        else:raise AssertionError('accepted malformed ordering/shape')
    meta['capture']={'profile':proof['profile'],'directory':str(directory),'proof_sha256':hashlib.sha256((directory/'proof.json').read_bytes()).hexdigest(),'statement_sha256':hashlib.sha256((directory/'statement.json').read_bytes()).hexdigest()}
    meta['joint_point']=joined
    path=out/(directory.name+'-metadata.json');path.write_text(json.dumps(meta,separators=(',',':')))
    def record(v):return '{ '+', '.join(k+' := '+str(x) for k,x in v.items())+' }'
    lean='import NearCompression.GKRMetadataValidity\nopen NearCompression\ndef capturedLayout : GKRJointLayout := '+record(l)+'\ndef capturedTables : List GKRTableMetadata := ['+',\n'.join(record(t) for t in meta['tables'])+']\ndef main : IO Unit := do\n  if !(capturedTables.all (gkrTableMetadataCheck capturedLayout)) then throw (IO.userError \"metadata rejected\")\n  IO.println s!\"PASS {capturedTables.length} table certificates\"\n'
    (out/(directory.name+'-check.lean')).write_text(lean)
    return dict(status='PASS',capture=meta['capture'],layout=l,tables=len(spec['air']['tables']),counts=counts,seconds=time.perf_counter()-started,metadata=str(path),scope='Captured observed input dimension, not deployment of fixed-envelope profile. No PCS/cryptographic soundness claim.')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--reference-dir',required=True);ap.add_argument('--capture',action='append',required=True);ap.add_argument('--output',required=True);a=ap.parse_args();sys.path.insert(0,a.reference_dir)
    import pq384_terminal_input_weights as weights
    import pq384_derived_weight_joint as derived
    from check_whir_handoff import ZERO,ONE,add,sub,mul
    out=Path(a.output);out.mkdir(parents=True,exist_ok=True);reports=[]
    for capture in a.capture:
        report=run(Path(capture),out);reports.append(report);print(json.dumps(report),flush=True)
        (out/'report.json').write_text(json.dumps(reports,indent=2))
