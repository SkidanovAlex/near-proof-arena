"""Verify a saved diagnostic one-fold proof without access to source rows."""
import json
from pathlib import Path
import sys
from pq384_one_fold import verify

proof=json.loads(Path(sys.argv[1]).read_text())
expected=json.loads(Path(sys.argv[2]).read_text())
for key in ('statement','parent_binding','expected_root'):
    expected[key]=bytes.fromhex(expected[key])
if not verify(proof,**expected):raise SystemExit('rejected')
print('PASS: diagnostic one-fold opening; no security-level certification')
