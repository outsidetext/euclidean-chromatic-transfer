"""Independent rigorous verifier for lattice-configuration certificates (Erdos #188).

Configurations live in the triangular lattice {m + n w}, w = e^{i pi/3}; squared distance of (m,n) is m^2+mn+n^2.
Valid pattern on a block: red set has no two points at distance 1, and every k-term AP x, x+u, ..., x+(k-1)u
(u one of the 6 unit lattice vectors) lying in the block contains a red point.
Certificate: per block (z, a, y), global lam. Checks:
 (C1) z + sum a_i s_i + sum y_ij s_i s_j >= 0 for every valid pattern (exact)
 (C2) h(t) = sum_D Y_D J0(sqrt(D) t) <= lam for all t >= 0 (arb balls on adaptive cells; tail |J0(x)|<=sqrt(2/(pi x)))
 (C3) q(delta) = sum z + delta sum a + delta^2 sum Y + lam (delta - delta^2) < 0 on the claimed interval (exact)
Intervals must cover [0,1].  Soundness: E[C1] >= 0, and sum_D Y_D F(sqrt D) = a0 h(0) + int h dnu <= lam delta + delta^2 (h(0)-lam).
usage: verify2d.py certs.json [k_expected]"""
import sys, json
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 80

UNITS = [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]
def d2(p, q):
    m, n = p[0]-q[0], p[1]-q[1]; return m*m + m*n + n*n

def valid_patterns(pts, k):
    """Generic backtracking: constraints checked once all their points are assigned."""
    n = len(pts); idx = {p: i for i, p in enumerate(pts)}
    cons = []   # ('edge', i, j) or ('ap', tuple)
    for i in range(n):
        for j in range(i+1, n):
            if d2(pts[i], pts[j]) == 1: cons.append(('edge', (i, j)))
    seen = set()
    for p in pts:
        for u in UNITS:
            ap = [(p[0]+t*u[0], p[1]+t*u[1]) for t in range(k)]
            if all(q in idx for q in ap):
                key = tuple(sorted(idx[q] for q in ap))
                if key not in seen: seen.add(key); cons.append(('ap', key))
    by_last = [[] for _ in range(n)]
    for kind, vs in cons: by_last[max(vs)].append((kind, vs))
    out = []; s = [None]*n
    def ok(i):
        for kind, vs in by_last[i]:
            if kind == 'edge' and s[vs[0]] == 1 and s[vs[1]] == 1: return False
            if kind == 'ap' and all(s[v] == 0 for v in vs): return False
        return True
    def rec(i):
        if i == n: out.append(tuple(s)); return
        for val in (0, 1):
            s[i] = val
            if ok(i): rec(i+1)
        s[i] = None
    rec(0)
    return out, len(seen)

def arbfr(x): return arb(x.numerator) / arb(x.denominator)

def check_C2(Y, lam):
    Ds = sorted(D for D in Y if Y[D] != 0)
    Ya = {D: arbfr(Y[D]) for D in Ds}; sq = {D: arb(D).sqrt() for D in Ds}
    lam_a = arbfr(lam)
    S = sum(abs(float(Y[D])) / D ** 0.25 for D in Ds)
    T = int((2 / 3.141592653589793) * (S / float(lam)) ** 2 * 1.02) + 2
    tail = sum((abs(Ya[D]) * (arb(2) / (arb.pi() * sq[D] * T)).sqrt() for D in Ds), arb(0))
    assert tail.upper() < lam_a.lower(), "tail bound failed"
    M2 = sum((abs(Ya[D]) * D for D in Ds), arb(0))   # |J0''| <= 1
    stack = [(Fr(0), Fr(T))]; cells = 0
    while stack:
        lo, hi = stack.pop()
        c = (lo + hi) / 2; r = (hi - lo) / 2
        ca, ra = arbfr(c), arbfr(r)
        h = sum((Ya[D] * (ca * sq[D]).bessel_j(0) for D in Ds), arb(0))
        hp = sum((Ya[D] * sq[D] * (ca * sq[D]).bessel_j(1) for D in Ds), arb(0))
        ub = h + abs(hp) * ra + M2 * ra * ra / 2
        if ub.upper() < lam_a.lower(): cells += 1; continue
        if r < Fr(1, 10**8): raise AssertionError(f"C2 fails near t={float(c)}: h={h}")
        stack += [(lo, c), (c, hi)]
    return T, cells

certs = json.load(open(sys.argv[1]))
kexp = int(sys.argv[2]) if len(sys.argv) > 2 else None
covered = []; patcache = {}
for ci, C in enumerate(certs):
    k = C['k']; lam = Fr(C['lam']); assert lam >= 0
    if kexp is not None: assert k == kexp
    Ztot = Fr(0); Atot = Fr(0); Y = {}
    for B in C['blocks']:
        pts = [tuple(p) for p in B['points']]; m = len(pts)
        assert len(set(pts)) == m
        key = (tuple(pts), k)
        if key not in patcache: patcache[key] = valid_patterns(pts, k)
        P, naps = patcache[key]
        z = Fr(B['z']); a = [Fr(x) for x in B['a']]; assert len(a) == m
        y = {tuple(map(int, kk.split(','))): Fr(x) for kk, x in B['y'].items()}
        for (i, j) in y: assert 0 <= i < j < m
        for s in P:
            red = [i for i in range(m) if s[i]]
            val = z + sum(a[i] for i in red) + sum(y.get((red[x], red[w]), 0) for x in range(len(red)) for w in range(x+1, len(red)))
            assert val >= 0, f"C1 fails on {s}"
        for (i, j), x in y.items():
            D = d2(pts[i], pts[j]); Y[D] = Y.get(D, Fr(0)) + x
        Ztot += z; Atot += sum(a)
        print(f"  cert {ci} block: {m} pts, {naps} {k}-APs, {len(P)} valid patterns, C1 ok", flush=True)
    T, cells = check_C2(Y, lam)
    Btot = sum(Y.values()); assert Btot <= lam
    lo, hi = Fr(C['claimed'][0]), Fr(C['claimed'][1])
    q = lambda d: Ztot + Atot * d + Btot * d * d + lam * (d - d * d)
    pts_ = [lo, hi]; c2, c1 = Btot - lam, Atot + lam
    if c2 != 0:
        v = -c1 / (2 * c2)
        if lo < v < hi: pts_.append(v)
    assert all(q(p) < 0 for p in pts_), "C3 fails"
    covered.append((lo, hi))
    print(f"cert {ci}: k={k} C2 ok (T={T}, {cells} cells), C3 ok on [{float(lo):.4f},{float(hi):.4f}]", flush=True)
covered.sort(); x = Fr(0)
for lo, hi in covered:
    assert lo <= x, f"gap at {float(x)}"; x = max(x, hi)
assert x >= 1
k = certs[0]['k']
print(f"ALL CHECKS PASSED: no admissible delta in [0,1]; every coloring has a blue unit-step {k}-AP, so the answer to #188 is >= {k+1}.")
