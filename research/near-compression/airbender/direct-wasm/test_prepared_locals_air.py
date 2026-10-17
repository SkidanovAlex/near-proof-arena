"""Actual prepared execution versus independent AIR semantics; no PCS claim."""
import argparse, copy, json, sys
from pathlib import Path
import prepared_locals_air as a
p=argparse.ArgumentParser()
p.add_argument('--reference-dir',required=True)
p.add_argument('--fixture',required=True)
p.add_argument('--legacy',action='append',default=[])
p.add_argument('--out',required=True)
args=p.parse_args();sys.path.insert(0,args.reference_dir)
from reference import inspect,expr_degree
out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
cases=json.load(open(args.fixture))['cases']
for name in args.legacy:cases+=json.load(open(name))['cases']
reports=[];attacks=[]
for case in cases:
    spec,rows=a.make(case);name=case['label']
    result=inspect(spec['air'],rows,spec['public'])
    assert result['accepted'],(name,result['violations'][:3])
    (out/(name+'-spec.json')).write_text(json.dumps(spec))
    (out/(name+'-rows.json')).write_text(json.dumps({'rows_by_table':rows}))
    def reject(label,bad=None,pub=None):
        result=inspect(spec['air'],rows if bad is None else bad,spec['public'] if pub is None else pub)
        assert not result['accepted'],(name,label)
        attacks.append(dict(case=name,attack=label))
    locals_count=len(case['entry_after']['frames'][0]['locals'])
    if locals_count:
        # Re-encode whole 32-bit words, preserving all Boolean range checks.
        for r in sorted({0,1,len(case['exec_rows']),len(rows[0])-1}):
            for index in range(locals_count):
                bad=copy.deepcopy(rows)
                old=sum(bad[0][r][a.LOCALS+32*index+b]<<b for b in range(32))
                a.putbits(bad[0][r],a.LOCALS+32*index,old^1,32)
                reject(f'coherent-local-word-{r}-{index}',bad)
        for r,event in enumerate(case['exec_rows']):
            op=event['instruction']['opcode'];index=event['instruction']['immediate']
            if op not in (32,33,34):continue
            bad=copy.deepcopy(rows);bad[0][r][a.LSEL:a.LSEL+4]=[0]*4
            wrong=(index+1)%locals_count;bad[0][r][a.LSEL+wrong]=1
            reject(f'wrong-selected-local-{r}',bad)
            # Coherent immediate/index forgery remains tied to CODE via bus.
            a.putbits(bad[0][r],a.IMM,wrong,32)
            reject(f'wrong-authenticated-local-index-{r}',bad)
            if event['status']!='continue':continue
            if op==32:
                bad=copy.deepcopy(rows);slot=len(event['before']['stack'])
                value=a.val(event['after']['stack'][slot])
                a.putbits(bad[0][r+1],a.STACK+32*slot,value^1,32)
                reject(f'wrong-get-push-{r}',bad)
            elif op==33:
                bad=copy.deepcopy(rows)
                old=a.val(event['before']['frames'][0]['locals'][index])
                a.putbits(bad[0][r+1],a.LOCALS+32*index,old,32)
                reject(f'set-did-not-write-{r}',bad)
            else:
                bad=copy.deepcopy(rows);slot=len(event['before']['stack'])-1
                a.putbits(bad[0][r+1],a.STACK+32*slot,0,32)
                reject(f'tee-popped-stack-{r}',bad)
        first=next(e for e in case['exec_rows'] if e['instruction']['opcode'] in (32,33,34))
        pc=first['pc'];alias=first['instruction']['immediate']+a.P
        bad=copy.deepcopy(rows);pub=spec['public'][:]
        a.putbits(bad[1][pc],a.CIMM,alias,32)
        for row in bad[0]:
            if sum(row[a.PC+b]<<b for b in range(32))==pc:a.putbits(row,a.IMM,alias,32)
        pub[a.CODEPUB+a.RECORD*pc+8]=alias%65536
        pub[a.CODEPUB+a.RECORD*pc+9]=alias//65536
        reject('coherent-field-alias-local-index',bad,pub)
        bad=copy.deepcopy(rows);bad[0][0][a.LOCALS]=2
        reject('nonboolean-local',bad)
    # Every newly published tag is authenticated, even for skipped code.
    for pc in range(len(case['code'])):
        for field in range(29,32):
            pub=spec['public'][:];pub[a.CODEPUB+a.RECORD*pc+field]^=1
            reject(f'public-local-tag-{pc}-{field}',pub=pub)
    reports.append(dict(label=name,local_count=locals_count,code=len(case['code']),
      executed=len(case['exec_rows']),error=case['error'],widths=[t['width'] for t in spec['air']['tables']],
      constraints=[len(t['constraints']) for t in spec['air']['tables']],
      degrees=[max(expr_degree(e,t['width'],spec['air']['numPub']) for e in t['constraints']) for t in spec['air']['tables']]))
report=dict(status='PASS',cases=reports,rejected=len(attacks),attacks=attacks,
    limitations=['Diagnostic source AIR/reference checks, not cryptographic proof verification.',
      'Actual prepare/step/runCall fixtures plus semantic interfaces; new AIR-to-step refinement remains pending.',
      'Stack8, four i32 locals, zero parameters, one defined function and one nested void block.',
      'PREP/CODE/local-count provenance checker for this version remains pending; public CODE is linear.'])
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='attacks'}))
