"""Standalone verification: 30-vertex 6-chromatic {1, sqrt3} two-distance graph.

Claim: the 30 points below (exact coordinates in Q(sqrt3, sqrt5)) admit no
proper 5-coloring when every pair at Euclidean distance exactly 1 or exactly
sqrt(3) must receive distinct colors; 6 colors suffice. Hence
chi(R^2; {1, sqrt3}) >= 6 via a 30-vertex witness
(previous smallest known 6-chromatic two-distance graphs: 31 vertices for
{1, golden ratio} [Parts 2020], 33 vertices for {1, sqrt3} [De Neve et al.,
Amer. Math. Monthly 132(10), 2025]).

Vertex encoding: [a0 a1 a2 a3] represents the point
    ( (a0 + a1*sqrt5)/8 , (a2*sqrt3 + a3*sqrt15)/8 ).
All arithmetic below is exact over integers: for a difference vector
(p, q, r, s), the squared distance times 64 equals
    p^2 + 5 q^2 + 3 r^2 + 15 s^2  +  (2 p q + 6 r s) * sqrt5,
so an edge of length 1 means (64, 0) and length sqrt3 means (192, 0).

Requires: pip install python-sat
"""
VECS = [
    (-6, 0, -2, 0), (-5, -3, -1, 1), (-5, 3, -3, 1), (-4, 0, -2, 2),
    (-4, 0, 0, 0), (-4, 0, 0, 4), (-3, -3, -1, 3), (-3, -3, 1, 1),
    (-3, 3, -1, 1), (-2, 0, -2, 4), (-2, 0, 0, 2), (-1, -3, -3, 3),
    (-1, -3, -1, 1), (-1, -3, 1, 3), (-1, 3, -1, 3), (-1, 3, 1, 1),
    (-1, 3, 3, 3), (0, 0, -2, 2), (0, 0, 0, 0), (0, 0, 2, 2),
    (1, -3, -3, 1), (1, -3, 1, 1), (1, 3, -1, 1), (1, 3, 3, 1),
    (2, 0, -2, 0), (2, 0, 0, 2), (2, 0, 2, 0), (3, -3, 1, 3),
    (3, 3, -1, 3), (4, 0, 0, 4),
]

def edges():
    out = []
    for i in range(30):
        for j in range(i + 1, 30):
            p, q, r, s = (VECS[i][k] - VECS[j][k] for k in range(4))
            rat = p * p + 5 * q * q + 3 * r * r + 15 * s * s
            irr = 2 * p * q + 6 * r * s
            if irr == 0 and rat in (64, 192):
                out.append((i, j))
    return out

def colorable(k, E, skip=None):
    from pysat.solvers import Cadical195
    s = Cadical195()
    for v in range(30):
        if v == skip:
            continue
        s.add_clause([v * k + c + 1 for c in range(k)])
    for u, v in E:
        if skip in (u, v):
            continue
        for c in range(k):
            s.add_clause([-(u * k + c + 1), -(v * k + c + 1)])
    return s.solve()

if __name__ == '__main__':
    assert len(set(VECS)) == 30
    E = edges()
    u1 = sum(1 for i, j in E
             if (lambda p, q, r, s: p*p + 5*q*q + 3*r*r + 15*s*s)(
                 *(VECS[i][k] - VECS[j][k] for k in range(4))) == 64)
    print(f'{len(E)} edges ({u1} at distance 1, {len(E)-u1} at sqrt3)')
    print('5-colorable:', colorable(5, E))
    print('6-colorable:', colorable(6, E))
    crit = all(colorable(5, E, skip=v) for v in range(30))
    print('vertex-critical (all 29-vertex subgraphs 5-colorable):', crit)
    ok = (not colorable(5, E)) and colorable(6, E) and crit
    print('VERIFIED' if ok else 'FAILED')
