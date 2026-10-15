import json, sys
from fractions import Fraction as F
d = json.load(open(sys.argv[1])); conv = sys.argv[2]
B = [[float(F(x)) for x in r] for r in d['B']]
if conv == 'rows': b1, b2 = B[0], B[1]
else: b1, b2 = [B[0][0], B[1][0]], [B[0][1], B[1][1]]
print(b1[0], b1[1], b2[0], b2[1]); print(len(d['polys']))
for P, c in zip(d['polys'], d['cols']):
    print(c, len(P), ' '.join(f'{float(F(x))!r} {float(F(y))!r}' for x, y in P))
