"""1-D coverage in rho = shortest/longest over certificate files (family reduction, NOTES.md s.1).
Accepts verify_box lists with degenerate b-box [1,1] (covers a-interval), and 173-pattern-int-v1/v2 lists.
usage: cover1d.py LO HI files..."""
import sys, json
from fractions import Fraction as F
lo, hi = F(sys.argv[1]), F(sys.argv[2]); iv = []
for fn in sys.argv[3:]:
    for c in json.load(open(fn)):
        if 'box' in c:
            assert F(c['box'][1][0]) == 1 and F(c['box'][1][1]) == 1, "not a strip (b-box must be [1,1])"
            iv.append((F(c['box'][0][0]), F(c['box'][0][1]), fn))
        else: iv.append((F(c['rho'][0]), F(c['rho'][1]), fn))
iv.sort(); reach = lo
for a, b, fn in iv:
    if a > reach: break
    reach = max(reach, b)
print(f"{len(iv)} intervals; contiguous coverage from {float(lo)} up to {float(reach):.6f} ({reach})" + ("  COVERS TARGET" if reach >= hi else f"  gap at {float(reach):.6f}"))
