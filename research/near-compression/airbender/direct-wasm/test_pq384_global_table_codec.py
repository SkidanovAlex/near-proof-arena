"""Full-height complete table binary bounds, statement binding and roundtrip."""
import copy,json,sys,hashlib
from pathlib import Path
from pq384_global_table_codec import decode,encode,shape,P
r=Path(sys.argv[1]);s=json.loads((r/'statement.json').read_text());spec=s['spec'];root=bytes.fromhex(s['root']);wire=(r/'proof.bin').read_bytes()
p=decode(wire,spec,root);assert p==json.loads((r/'proof.json').read_text()) and encode(p,spec,root)==wire
rejects=[]
def reject(label,b=wire,sp=spec,rt=root):
    try:decode(b,sp,rt)
    except ValueError as e:rejects.append(dict(case=label,reason=str(e)))
    else:raise AssertionError('accepted '+label)
for i in range(32):reject('truncate'+str(i),wire[:len(wire)*i//32])
reject('last byte missing',wire[:-1]);reject('extra byte',wire+b'\0');reject('magic',b'X'+wire[1:])
n,w,d,fixed,lo,hi=shape(spec)
for label,pos in [('constraint',6),('current',6+16*n*(d+2)),('next',6+16*(n*(d+2)+w)),
                  ('shift',6+16*(n*(d+2)+2*w)),('claims',fixed-16*w),('PCS header',fixed),('PCS leaf/path',len(wire)-1)]:
    b=bytearray(wire);b[pos]^=1;reject(label,bytes(b))
b=bytearray(wire);b[6:10]=P.to_bytes(4,'little');reject('noncanonical field',bytes(b))
reject('external root',rt=bytes([root[0]^1])+root[1:])
sp=copy.deepcopy(spec);sp['public'][0]=(sp['public'][0]+1)%P;reject('public',sp=sp)
sp=copy.deepcopy(spec);sp['terminal_degree']=64;reject('terminal profile',sp=sp)
report=dict(status='PASS',binary_bytes=len(wire),binary_sha256=hashlib.sha256(wire).hexdigest(),negative_checks=len(rejects),cases=rejects,
 scope='Complete table-local diagnostic payload; external spec/root; not global bus or security proof')
(r/'codec-regressions.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS:',len(rejects),'rejections')
