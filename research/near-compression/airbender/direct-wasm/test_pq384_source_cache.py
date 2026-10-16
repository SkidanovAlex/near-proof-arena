"""Native cached full-height source commitment, independent encoding checks."""
import json,struct,subprocess,sys,tempfile,time
from pathlib import Path
from pq384_source_cache import SourceCache
from pq384_primitives import P
from test_pq384_packing import pair

binary,source,report=sys.argv[1:]
rows=json.loads(Path(source).read_text())['rows'];n=len(rows);width=len(rows[0]);packing=32
degree=n*packing;lanes=(width+packing-1)//packing
work=Path(tempfile.mkdtemp(prefix='near-pq384-source-cache-'));cache=work/'cache'
indices=[0,13,2*degree-1]
(work/'input.json').write_text(json.dumps({'rows':rows,'packing':packing,'indices':indices,'cache_directory':str(cache)}))
start=time.monotonic()
subprocess.run([binary,str(work/'input.json'),str(work/'output.json')],check=True,capture_output=True)
elapsed=time.monotonic()-start;out=json.loads((work/'output.json').read_text())
root=struct.pack('<12I',*out['root']);args=dict(expected_root=root,log_rows=n.bit_length()-1,width=width,packing=packing)
coefficient_checks=0
with SourceCache(cache,**args) as cached:
    for i,opened in zip(indices,out['openings']):
        actual=cached.opening(i)
        assert actual=={'leaf':opened['leaf'],'path':[struct.pack('<12I',*p).hex() for p in opened['path']]}
        assert actual['leaf']==pair(rows,packing,out['omega'],i)
    for lane in sorted(set([0,lanes//2,lanes-1])):
        coeff=cached.coefficients(lane)
        for mask in [0,1,63,256,degree-1]:
            total=0;subset=mask
            while True:
                col=lane*packing+subset//n;value=rows[subset%n][col] if col<width else 0
                total+=(-1 if (mask.bit_count()-subset.bit_count())%2 else 1)*value
                if subset==0:break
                subset=(subset-1)&mask
            assert coeff[mask]==total%P;coefficient_checks+=1
rejected=0
for key,value in [('expected_root',bytes([root[0]^1])+root[1:]),('width',width+1),('packing',16)]:
    bad=args.copy();bad[key]=value
    try:
        with SourceCache(cache,**bad):pass
    except ValueError:rejected+=1
    else:raise AssertionError('wrong cache identity accepted')
for filename,offset,replacement,action in [
    ('tree.sha384',0,b'\xff',lambda c:c.opening(1)),
    ('coefficients.u32',0,P.to_bytes(4,'little'),lambda c:c.coefficients(0))]:
    path=cache/filename
    with path.open('r+b') as file:
        file.seek(offset);old=file.read(len(replacement));file.seek(offset);file.write(replacement);file.flush()
    try:
        try:
            with SourceCache(cache,**args) as c:action(c)
        except ValueError:rejected+=1
        else:raise AssertionError('corrupt cache accepted')
    finally:
        with path.open('r+b') as file:file.seek(offset);file.write(old)
result={'status':'PASS','rows':n,'width':width,'packing':packing,'lanes':lanes,
        'cache_directory':str(cache),'root_hex':root.hex(),'native_seconds_including_io':elapsed,
        'cache_bytes':sum(p.stat().st_size for p in cache.iterdir()),
        'independent_full_vector_pairs':len(indices),'independent_coefficients':coefficient_checks,
        'negative_checks':rejected,
        'scope':'Full-height source commitment cache; not a complete opening proof or AIR proof',
        'limits':['Coefficient file remains untrusted prover data','Only sampled pairs/coefficients independently checked',
                  'Single-run shared-host timing; no128-bitsecurity claim']}
Path(report).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
