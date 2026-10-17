"""Full-height serialization boundaries; synthetic bytes are NOT a valid proof."""
import json
from pq384_batched_codec import MAGIC, expected_size, decode, encode, dimensions
from pq384_batched_fold import public, oracle_context

shape=(13,544,32)
# Build the externally fixed wire shape independently from codec helpers.
degree=262144
size=len(MAGIC)+64*16
rounds=0
while degree>64:
    source_words=34 if rounds==0 else 8
    source_depth=(2*degree).bit_length()-1
    next_depth=degree.bit_length()-1
    size+=3*16+48+8*(4*source_words+48*source_depth+32+48*next_depth)
    degree//=2
    rounds+=1
assert rounds==12 and expected_size(*shape)==size
wire=MAGIC+bytes(size-len(MAGIC))
proof=decode(wire,*shape)
assert len(proof['rounds'])==12 and encode(proof,*shape)==wire
rejections=0
for bad in [(14,1,1),(13,544,64),(13,2081,32),(13,544,3)]:
    try:dimensions(*bad)
    except ValueError:rejections+=1
    else:raise AssertionError('accepted unsupported shape')
for bad in [wire[:-1],wire+b'\0']:
    try:decode(bad,*shape)
    except ValueError:rejections+=1
    else:raise AssertionError('accepted wrong length')
args=dict(statement=b'full-height-shape-test',parent_binding=b'test',expected_root=bytes(48),
          log_rows=13,width=544,packing=32,row_point=[(0,0,0,0)]*13,
          column_claims=[(0,0,0,0)]*544)
h,t,d=public(args)
assert d==262144 and len(h['lane_claims'])==17
for d in [128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144]:
    ctx,omega=oracle_context(b'shape-test',d)
    assert ctx and pow(omega,4*d,2013265921)==1 and pow(omega,2*d,2013265921)!=1
print(json.dumps(dict(status='PASS',shape=shape,rounds=rounds,binary_shape_bytes=size,
    malformed_rejections=rejections,oracle_domains_checked=12,
    scope='Synthetic codec roundtrip and domain bounds only; no valid proof or security claim'),indent=2))
