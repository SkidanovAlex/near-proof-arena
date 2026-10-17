"""Analyze the executed Merkle hash DAG, not a claimed globally optimal multiproof."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,shutil
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/native-literal-merkle-reconstruction'
SOURCE=ROOT/'results/native-literal-sha384-alllist-rate7'
raw=(SOURCE/'child.proof').read_bytes()
source_report=json.loads((SOURCE/'report.json').read_text())
assert hashlib.sha256(raw).hexdigest()==source_report['sha256']['child.proof']
auth=(SOURCE/'auth-digests.bin').read_bytes();assert len(auth)%48==0
targets=set(auth[i:i+48] for i in range(0,len(auth),48))
trace_path=OUT/'merkle-trace.bin'
trace=trace_path.read_bytes() if trace_path.exists() else gzip.decompress((OUT/'merkle-trace.bin.gz').read_bytes())
graph={};pos=0;counts=Counter()
while pos<len(trace):
    assert pos+5<=len(trace)
    kind=trace[pos];n=int.from_bytes(trace[pos+1:pos+5],'little');pos+=5
    assert pos+n+48<=len(trace)
    payload=trace[pos:pos+n];pos+=n;digest=trace[pos:pos+48];pos+=48
    counts[kind]+=1
    if kind==0:
        message=b'nearproof-native-sha384-ext12-v4'+b'\0'+len(payload).to_bytes(8,'little')+payload
    else:
        assert kind==1 and n==96
        message=b'NPQ4NODE'+payload
    assert hashlib.sha384(message).digest()==digest
    assert digest not in graph or graph[digest]==(kind,payload)
    graph[digest]=(kind,payload)
assert [counts[0],counts[1]]==source_report['verifier_hash_cost']['calls'][:2]
# Find every exact authentication-digest occurrence in the native proof. Leaf
# inputs must be available outside these omitted slots, not circular references.
holes=[];i=0
while i<len(raw):
    if raw[i:i+48] in targets:holes.append((i,i+48));i+=48
    else:i+=1
assert len(holes)*48==len(auth)
def leaf_offset(payload):
    start=0
    while payload and (offset:=raw.find(payload,start))>=0:
        if all(offset+len(payload)<=a or b<=offset for a,b in holes):return offset
        start=offset+1
    return None
seen={};visiting=set();plan=[]
def visit(digest):
    if digest in seen:return seen[digest]
    assert digest not in visiting
    visiting.add(digest)
    if digest in graph:
        kind,payload=graph[digest]
        if kind==1:
            left=visit(payload[:48]);right=visit(payload[48:])
            entry=dict(kind='node',left=left,right=right)
        elif (offset:=leaf_offset(payload)) is not None:
            entry=dict(kind='leaf',offset=offset,length=len(payload))
        else:entry=dict(kind='frontier',digest=digest.hex())
    else:entry=dict(kind='frontier',digest=digest.hex())
    visiting.remove(digest)
    index=len(plan);seen[digest]=index;plan.append(entry);return index
for target in sorted(targets):visit(target)
# Independently evaluate the plan from a native byte skeleton with all auth slots
# zeroed. No original authentication value is available except retained frontier.
skeleton=bytearray(raw)
for a,b in holes:skeleton[a:b]=bytes(48)
values=[]
for i,entry in enumerate(plan):
    if entry['kind']=='frontier':value=bytes.fromhex(entry['digest'])
    elif entry['kind']=='leaf':
        payload=skeleton[entry['offset']:entry['offset']+entry['length']]
        value=hashlib.sha384(b'nearproof-native-sha384-ext12-v4'+b'\0'+len(payload).to_bytes(8,'little')+payload).digest()
    else:
        assert entry['left']<i and entry['right']<i
        value=hashlib.sha384(b'NPQ4NODE'+values[entry['left']]+values[entry['right']]).digest()
    values.append(value)
for target in targets:assert values[seen[target]]==target
reconstructed=bytearray(skeleton)
for a,b in holes:reconstructed[a:b]=values[seen[raw[a:b]]]
assert reconstructed==raw
count=Counter(e['kind'] for e in plan)
# Concrete simple instruction-cost model: 1-byte opcode, 2-byte prior-entry
# references, 4-byte source offsets/lengths. This is not an implemented codec.
assert len(plan)<=65536
program_bytes=49*count['frontier']+9*count['leaf']+5*count['node']
non_auth_bytes=len(raw)-len(auth)
request_bytes=source_report['request_bytes']
report=dict(status='EXECUTED_MERKLE_DAG_RECONSTRUCTION_ANALYSIS',
    native_proof_sha256=hashlib.sha256(raw).hexdigest(),trace_sha256=hashlib.sha256(trace).hexdigest(),
    actual_trace_calls=dict(leaves=counts[0],nodes=counts[1]),unique_trace_outputs=len(graph),
    unique_authentication_targets=len(targets),authentication_occurrences=len(holes),
    closure_counts=dict(count),all_leaf_sources_outside_omitted_auth_slots=True,
    exact_reconstruction_from_zeroed_auth_skeleton=True,
    native_non_auth_bytes=non_auth_bytes,
    frontier_digest_bytes=48*count['frontier'],
    fixed_plan_payload_plus_request_ignoring_metadata=non_auth_bytes+48*count['frontier']+request_bytes,
    simple_instruction_program_bytes=program_bytes,
    simple_encoding_bytes_before_headers=non_auth_bytes+program_bytes+3*len(holes),
    current_dictionary_bytes=json.loads((ROOT/'results/native-literal-alllist-rate7-dictionary/report.json').read_text())['wire_bytes'],
    decision='Do not adopt the naive explicit-DAG encoding; pursue an additional protocol-level reduction.',
    limitations=['fixed captured verification DAG, not global reconstruction optimum',
        'unchanged non-authentication byte payload in this accounting',
        'known algebraic/padding structure outside captured operations not explored',
        'instruction model is not a serialized verified wire artifact',
        'no QROM certificate, recursive parent, full NEAR or new Lean theorem'],security_certified=False)
(OUT/'plan.json.gz').write_bytes(gzip.compress(json.dumps(plan,separators=(',',':')).encode(),mtime=0))
(OUT/'merkle-trace.bin.gz').write_bytes(gzip.compress(trace,mtime=0))
if trace_path.exists():trace_path.unlink()
shutil.copyfile('/tmp/nearproof-merkle-trace.log',OUT/'replay.log')
for name in ['main.rs','native_sha384_config.rs']:
    shutil.copyfile('/tmp/nearproof-native-sha384/src/'+name,OUT/name)
report['artifact_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in OUT.iterdir() if p.is_file() and p.name!='report.json'}
(OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
