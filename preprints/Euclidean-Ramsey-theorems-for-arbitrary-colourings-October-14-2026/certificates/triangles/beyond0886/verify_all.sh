#!/bin/sh
# Author's re-verification of the 1-D certification (family reduction, see README.md):
# strip boxes with verify_box.py, interval certificates with check_beyond.py, coverage with cover1d.py.
# (Paths adapted from the research repository; the checks themselves are unchanged.)
# usage: sh verify_all.sh        (set PY to a Python with python-flint, e.g. PY=~/venv/bin/python3)
PY=${PY:-python3}
cd "$(dirname "$0")" || exit 1
set -e
for f in strip_086125_0869.json strip_0869_0879.json; do out=$($PY verify_box.py $f); echo "$f: $(echo "$out" | tail -1)"; done
for f in int2_band_A.json int2_band_B.json; do
  $PY -c "
import json, sys
from check_beyond import check_int, check_int2
L = json.load(open('$f')); n = 0
for c in L:
    (check_int2 if c['type'] == '173-pattern-int-v2' else check_int)(c, verbose=False); n += 1
print('$f:', n, 'interval certificates VERIFIED')
"; done
$PY cover1d.py 689/800 17693/20000 strip_086125_0869.json strip_0869_0879.json int2_band_A.json int2_band_B.json
out=$($PY check_beyond.py iso0886_cfg17.json); echo "$out" | tail -1
