# Dictionary transport of all-list/blowup128 proof

Native proof512609bytes; self-contained dictionary450302bytes; with919-byte
request451221bytes. Same encoding and decoder as the earlier digest dictionary,
with459entries and1909references. Exact Python reconstruction, independent Rust
native replay without original proof/witnesses, Merkle-rejected digest mutation
and eight malformed-format checks passed. Security remains uncertified.

Reproduction after building the native profile:

```sh
NEARPROOF_ALL_LIST=1 NEARPROOF_LOG_BLOWUP=7 NEARPROOF_REPLAY=1 NEARPROOF_WHIR_CENSUS=1 NEARPROOF_LITERAL_OUT="$PWD/research/near-compression/results/native-literal-sha384-alllist-rate7" RAYON_NUM_THREADS=4 /tmp/nearproof-native-sha384/target/release/nearproof-native-sha384 > /tmp/nearproof-alllist-rate7-census.log
python3 research/near-compression/airbender/direct-wasm/check_digest_dictionary.py --source research/near-compression/results/native-literal-sha384-alllist-rate7 --out research/near-compression/results/native-literal-alllist-rate7-dictionary --census-log /tmp/nearproof-alllist-rate7-census.log
```

The source profile's report supplies explicit parameters for replay; no inherited
shell settings select them. The dictionary includes all its entries. Census
files are encoder evidence, not verifier inputs. FullNEAR and recursive-proof
claims do not follow from this retained bounded slice.
