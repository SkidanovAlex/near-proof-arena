"""Verify saved diagnostic multi-round proof with no source-row access."""
import json,sys
from pathlib import Path
from pq384_multi_fold import verify

proof=json.loads(Path(sys.argv[1]).read_text())
expected=json.loads(Path(sys.argv[2]).read_text())
for key in ('statement','parent_binding','expected_root'):
    expected[key]=bytes.fromhex(expected[key])
if not verify(proof,**expected):raise SystemExit('rejected')
print('PASS: diagnostic multi-round opening; no security-level certification')
