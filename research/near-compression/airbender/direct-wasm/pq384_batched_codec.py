"""Fixed-shape, canonical binary encoding for diagnostic batched openings.

Shape is supplied by the enclosing statement. Decoding is NOT verification.
No fields are omitted: profiles are fixed by magic; counts follow trusted shape.
"""
import struct
from pq384_primitives import P,require
from packed_claim_handoff import packing_context
from pq384_one_fold import decode_hash

MAGIC=b'NPBF\x00\x01'


def dimensions(log_rows,width,packing):
    packing_context(log_rows,width,packing)
    require(log_rows<=13,'codec row dimension')
    degree=(1<<log_rows)*packing;lanes=(width+packing-1)//packing
    require(128<=degree<=262144 and lanes<=64,'codec shape')
    return degree,lanes


def expected_size(log_rows,width,packing):
    d,lanes=dimensions(log_rows,width,packing);total=len(MAGIC)+1024;first=True
    while d>64:
        depth=d.bit_length()
        total+=96+8*((2*lanes if first else 8)*4+depth*48+32+(depth-1)*48)
        d//=2;first=False
    return total


def encode(proof,log_rows,width,packing):
    d,lanes=dimensions(log_rows,width,packing);initial=d;out=bytearray(MAGIC)
    require(type(proof)is dict and set(proof)=={'profile','rounds','terminal'} and
            proof['profile']=='near-pq384-batched-fold-v1','codec proof fields')
    require(isinstance(proof['rounds'],list) and len(proof['rounds'])==d.bit_length()-7,'codec rounds')
    def words(values,count):
        require(isinstance(values,list) and len(values)==count and
                all(type(v)is int and 0<=v<P for v in values),'codec field vector')
        out.extend(struct.pack('<'+'I'*count,*values))
    def extensions(values,count):
        require(isinstance(values,list) and len(values)==count,'codec extension vector')
        for v in values:words(v,4)
    def opening(value,count,depth):
        require(type(value)is dict and set(value)=={'leaf','path'},'codec opening fields')
        words(value['leaf'],count)
        require(isinstance(value['path'],list) and len(value['path'])==depth,'codec path length')
        for h in value['path']:out.extend(decode_hash(h))
    for rd in proof['rounds']:
        require(type(rd)is dict and set(rd)=={'quadratic','next_root','queries'},'codec round fields')
        extensions(rd['quadratic'],3);out.extend(decode_hash(rd['next_root']))
        require(isinstance(rd['queries'],list) and len(rd['queries'])==8,'codec queries')
        for q in rd['queries']:
            require(type(q)is dict and set(q)=={'source','next'},'codec query fields')
            opening(q['source'],2*lanes if d==initial else 8,d.bit_length())
            opening(q['next'],8,d.bit_length()-1)
        d//=2
    term=proof['terminal']
    require(type(term)is dict and set(term)=={'profile','coefficients'} and
            term['profile']=='near-pq384-terminal-v1' and
            isinstance(term['coefficients'],list) and len(term['coefficients'])==1,'codec terminal')
    extensions(term['coefficients'][0],64)
    require(len(out)==expected_size(log_rows,width,packing),'codec size invariant')
    return bytes(out)


def decode(data,log_rows,width,packing):
    require(type(data)is bytes and len(data)==expected_size(log_rows,width,packing),'codec byte length')
    require(data[:len(MAGIC)]==MAGIC,'codec magic');offset=len(MAGIC)
    d,lanes=dimensions(log_rows,width,packing);initial=d
    def read(count):
        nonlocal offset
        require(offset+count<=len(data),'codec truncation')
        result=data[offset:offset+count];offset+=count;return result
    def words(count):
        values=list(struct.unpack('<'+'I'*count,read(count*4)))
        require(all(v<P for v in values),'codec noncanonical field');return values
    def opening(count,depth):return {'leaf':words(count),'path':[read(48).hex() for _ in range(depth)]}
    rounds=[]
    while d>64:
        q=[words(4) for _ in range(3)];root=read(48).hex();queries=[]
        for _ in range(8):
            queries.append({'source':opening(2*lanes if d==initial else 8,d.bit_length()),
                            'next':opening(8,d.bit_length()-1)})
        rounds.append({'quadratic':q,'next_root':root,'queries':queries});d//=2
    proof={'profile':'near-pq384-batched-fold-v1','rounds':rounds,
           'terminal':{'profile':'near-pq384-terminal-v1','coefficients':[[words(4) for _ in range(64)]]}}
    require(offset==len(data),'codec trailing bytes')
    require(encode(proof,log_rows,width,packing)==data,'codec canonical roundtrip')
    return proof
