"""Exact verification of a deneve117_best<seed>.json candidate.

Vectors [a0..a7] -> ((a0+a1*s3+a2*s7+a3*s21)/8, (a4+a5*s3+a6*s7+a7*s21)/8).
Edge iff squared distance is exactly 1 or 2+sqrt3 (over Q(s3,s7,s21)).
Checks: no duplicates, not 5-colorable (CaDiCaL AND Glucose, unpinned),
6-colorable, vertex-critical.
"""
import json, sys
from pysat.solvers import Cadical195, Glucose42

path = sys.argv[1]
d = json.load(open(path))
V = [tuple(v) for v in d['vecs']]
n = len(V)
print(f'{path}: {n} vertices (claimed {d["size"]})')
assert len(set(V)) == n, 'DUPLICATES'

def sq(p, q, r, s):
    return (p*p + 3*q*q + 7*r*r + 21*s*s,
            2*p*q + 14*r*s, 2*p*r + 6*q*s, 2*p*s + 2*q*r)

E = []
n1 = 0
for i in range(n):
    for j in range(i + 1, n):
        diff = [V[i][k] - V[j][k] for k in range(8)]
        x = sq(*diff[:4]); y = sq(*diff[4:])
        tot = tuple(x[k] + y[k] for k in range(4))
        if tot == (64, 0, 0, 0):
            E.append((i, j)); n1 += 1
        elif tot == (128, 64, 0, 0):
            E.append((i, j))
print(f'exact edges: {len(E)} ({n1} unit, {len(E)-n1} at (sqrt2+sqrt6)/2)')

def colorable(k, cls, skip=None):
    s = cls()
    for v in range(n):
        if v == skip:
            continue
        s.add_clause([v * k + c + 1 for c in range(k)])
    for u, v in E:
        if skip in (u, v):
            continue
        for c in range(k):
            s.add_clause([-(u * k + c + 1), -(v * k + c + 1)])
    return s.solve()

c5a = colorable(5, Cadical195)
c5b = colorable(5, Glucose42)
c6 = colorable(6, Cadical195)
crit = all(colorable(5, Cadical195, skip=v) for v in range(n))
print(f'5-colorable: cadical={c5a} glucose={c5b}  6-colorable: {c6}  '
      f'vertex-critical: {crit}')
ok = (not c5a) and (not c5b) and c6
print(f'VERDICT: {"EXACTLY VERIFIED" if ok else "FAILED"} '
      f'{n}-vertex 6-chromatic {{1,(sqrt2+sqrt6)/2}} graph (De Neve 2025: 117)')
