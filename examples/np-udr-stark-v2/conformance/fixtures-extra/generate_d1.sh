#!/bin/sh
# Regenerates the extra D1a fixtures (./d1) deterministically (see gen_extra_d1a.py).
#   ./generate_d1.sh            # rewrites ./d1
#   ./generate_d1.sh /tmp/x     # or elsewhere
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-$HERE/d1}
BASE=$HERE/../../../../oracle/fixtures/v3/public-d1/d1
python3 "$HERE/gen_extra_d1a.py" r5 --base "$BASE/01-h10025-s1" --out "$OUT"
