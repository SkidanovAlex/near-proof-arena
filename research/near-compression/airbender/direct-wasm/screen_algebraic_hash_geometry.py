"""Necessary output-cardinality screen and explicitly uncertified hash geometry."""
import gzip
import hashlib
import json
import math
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[2]
P=2013265921


def main():
    manifest=ROOT/'results/hash-architecture-review/sources.json';sources=json.loads(manifest.read_text());texts={}
    for item in sources['code']:
        path=ROOT/item['snapshot'];raw=gzip.decompress(path.read_bytes())
        assert hashlib.sha256(raw).hexdigest()==item['raw_sha256']
        assert hashlib.sha256(path.read_bytes()).hexdigest()==item['snapshot_sha256']
        texts[item['path']]=raw.decode()
    params=texts['poseidon2/src/round_numbers.rs'];baby=texts['baby-bear/src/poseidon2.rs']
    assert 'M = 128' in params and 'poseidon2_round_numbers_128' in params
    rounds={int(w):int(n) for w,n in re.findall(r'BABYBEAR_POSEIDON2_PARTIAL_ROUNDS_(16|24|32): usize = (\d+)',baby)}
    assert rounds=={16:13,24:21,32:30} and math.gcd(7,P-1)==1
    minimum=next(n for n in range(1,33) if P**n>=1<<384)
    assert minimum==13 and P**12<1<<384
    digests=[]
    for n in [8,12,13,16]:
        digests.append(dict(field_elements=n,canonical_u32_bytes=4*n,max_range_log2=n*math.log2(P),
            ideal_generic_quantum_collision_work_exponent=n*math.log2(P)/3,
            passes_384_bit_output_range_screen=P**n>=1<<384,pq128_certified=False))
    candidates=[]
    for width,partial in rounds.items():
        capacity=minimum;rate=width-capacity;output=minimum
        # Hypothetical wrapper: two framing words, two child digests and one
        # delimiter; absorb whole rate blocks then squeeze additional outputs.
        input_words=2+2*output+1;absorbs=(input_words+rate-1)//rate
        extra_squeeze=(output+rate-1)//rate-1;perms=absorbs+extra_squeeze
        sboxes=8*width+partial
        candidates.append(dict(width=width,capacity_elements=capacity,rate_elements=rate,digest_elements=output,
            upstream_M=128,full_rounds=8,partial_rounds=partial,sboxes_per_permutation=sboxes,
            hypothetical_pair_hash_input_elements=input_words,absorb_permutations=absorbs,extra_squeeze_permutations=extra_squeeze,
            pair_hash_permutations=perms,x7_multiplications_per_permutation=4*sboxes,
            pair_hash_sbox_multiplications=4*sboxes*perms,pq128_certified=False))
    report=dict(status='ALGEBRAIC_HASH_GEOMETRY_ONLY_SECURITY_OPEN',field=P,minimum_output_elements_for_384_bit_range=minimum,digest_screens=digests,candidates=candidates,
        claims_not_established=['128-bit quantum security of the concrete permutation/round parameters','prime-field sponge/duplex quantum indifferentiability and concrete losses','binding/collapsing requirements for this PCS and adaptive Fiat-Shamir protocol','injective canonical field/byte framing and role separation','full recursive verifier proof size, NEAR semantics or capacity'],
        decision='Width32 with13output/13capacity elements is a cost-screen candidate, not an approved hash. Retain SHA384 baseline. Establish concrete quantum permutation assumptions/parameters and full protocol budget before substitution. Do not treat the upstream M128 selector as PQ128 or repair a narrow inner digest by wrapping it in SHA384.',
        scope='BHT ideal generic collision query scaling motivates a necessary output-range screen under unrestricted quantum-query modeling. Capacity13 is a conservative shape choice, not a security theorem. Upstream round counts only provide cost examples; no quantum algebraic-attack margin inferred. Pair wrapper is hypothetical; linear layers, routing, canonicalization and proof costs excluded. More field arithmetic does not introduce an elliptic-curve assumption.',
        sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),manifest]})
    (ROOT/'results/hash-architecture-review/geometry.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
