# Dictionary transport of the byte-packed AIR candidate

Native412097bytes; dictionary356150bytes; plus919-byte request357069bytes.
Independent Rust reconstruction/native verification, digest-mutation rejection
and malformed-input checks pass. Parameters, including interaction_log26, come
from the source profile report. This changed AIR now has a closed Lean semantic
refinement to the supported original Wasm slice; native acceptance-to-HoldsP
and quantum security remain unproved. Do not promote this
number to the prior unmodified-AIR baseline (451221bytes).

After building the packed profile, run its replay with NEARPROOF_WHIR_CENSUS=1,
NEARPROOF_N_STACK=15, NEARPROOF_ALL_LIST=1, NEARPROOF_LOG_BLOWUP=7 and
NEARPROOF_INTERACTION_LOG=26, writing /tmp/nearproof-byte-packed-census.log. Then:

```sh
python3 research/near-compression/airbender/direct-wasm/check_digest_dictionary.py --source research/near-compression/results/native-literal-byte-packed --out research/near-compression/results/native-literal-byte-packed-dictionary --census-log /tmp/nearproof-byte-packed-census.log
```

The dictionary is fully included. No trace/fixture/original proof is required
by replay. Security remains uncertified; the semantic slice refinement is recorded in
../native-literal-byte-packed/closed-certificate-check.json.
