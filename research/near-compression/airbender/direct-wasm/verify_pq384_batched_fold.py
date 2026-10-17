"""Verify saved diagnostic batched multi-round proof with no source-row access."""
import json,sys
from pathlib import Path
from pq384_batched_fold import verify

expected=json.loads(Path(sys.argv[2]).read_text())
for key in ('statement','parent_binding','expected_root'):
    expected[key]=bytes.fromhex(expected[key])
if sys.argv[3:]==['--binary']:
    from pq384_batched_codec import decode
    proof=decode(Path(sys.argv[1]).read_bytes(),expected['log_rows'],expected['width'],expected['packing'])
elif not sys.argv[3:]:
    proof=json.loads(Path(sys.argv[1]).read_text())
else:raise SystemExit('usage: proof statement [--binary]')
if not verify(proof,**expected):raise SystemExit('rejected')
print('PASS: diagnostic batched multi-round opening; no security-level certification')
