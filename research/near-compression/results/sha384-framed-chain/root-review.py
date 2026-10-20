import sys,json,hashlib,copy
from pathlib import Path
sys.path.insert(0,str(Path('airbender/direct-wasm').resolve()))
import verify_sha384_framed_chain as v
import pq384_global_bus_codec as codec
out=Path('results/sha384-framed-chain');generated=Path('/tmp/root-sha384-framed-chain')
trusted=json.loads((out/'captured-hash.json').read_text());items=json.loads((out/'chain-proof.json').read_text())
tag=bytes.fromhex(trusted['tag_hex']);parts=[bytes.fromhex(x) for x in trusted['parts_hex']];expected=bytes.fromhex(trusted['expected_digest_hex'])
message=v.frame(tag,parts,v.PREFIX)
assert message==bytes.fromhex(trusted['message_hex'])
assert hashlib.sha384(message).digest()==expected
chain=json.loads((generated/'chain.json').read_text());assert bytes(chain['message_bytes'])==message
assert bytes(chain['digest_bytes'])==expected
canonical=json.loads((generated/'block-0/spec.json').read_text())['air']
for i,item in enumerate(items):
 fresh=json.loads((generated/f'block-{i}/spec.json').read_text());assert fresh['air']==canonical==item['statement']['spec']['air'];assert fresh['public']==item['statement']['spec']['public']
 s=item['statement'];wire=(out/f'block-{i}/proof.bin').read_bytes()
 assert codec.decode(wire,s['spec'],[bytes.fromhex(x) for x in s['roots']])==item['proof']
assert v.verify(items,canonical,tag,parts,expected)
negative=0
for i in range(4):
 for limb in (0,32,96):
  bad=copy.deepcopy(items);pub=bad[i]['statement']['spec']['public'];pub[limb]^=1
  try:v.boundaries(bad,canonical,tag,parts,expected)
  except (ValueError,KeyError,TypeError,IndexError):negative+=1
  else:raise AssertionError((i,limb))
for bad in (items[:-1],items+items[-1:],items[::-1],items[1:]+items[:1]):
 try:v.boundaries(bad,canonical,tag,parts,expected)
 except (ValueError,KeyError,TypeError,IndexError):negative+=1
 else:raise AssertionError('invalid chain accepted')
report=dict(status='PASS',canonical_trace_regeneration=True,binary_decode_exact=True,full_chain_fresh_verification=True,independent_boundary_mutations=negative,compression_blocks=len(items),message_bytes=len(message),security_certified=False,scope='One exact framed SHA384 hash; external boundaries, not recursive verifier')
(out/'root-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
