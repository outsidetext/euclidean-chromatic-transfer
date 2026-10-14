# Independent check (Claude) of E^3 -> (l2, lk) line certificates: brute-force patterns, exact C1 incl. congruence,
# float grid + second-order bound for h(t) = Y1 Om3(t) + sum Y_D Om3(sqrt(D) t) <= lam, tail |Om3(x)| <= 1/x, exact C3.
import json, sys, itertools, math, numpy as np
from fractions import Fraction as Fr
d = json.load(open(sys.argv[1])); K = int(d['k']); cap = Fr(d['cap']); cov = []
def D2(p, q): s = sum((a-b)**2 for a, b in zip(p, q)); assert s % 2 == 0; return s//2
for ci, C in enumerate(d['certs']):
    lam = Fr(C['lam']); Y = {1: Fr(C['Y1'])}; Z = Fr(0); A = Fr(0)
    for B in C['blocks']:
        pts = [tuple(p) for p in B['points']]; n = len(pts)
        units = [(i, j) for i in range(n) for j in range(i+1, n) if D2(pts[i], pts[j]) == 1]
        idx = {p: i for i, p in enumerate(pts)}; aps = set()
        for i, j in units:
            for a_, b_ in ((i, j), (j, i)):
                u = tuple(x - y for x, y in zip(pts[b_], pts[a_]))
                ap = [tuple(x + m*w for x, w in zip(pts[a_], u)) for m in range(K)]
                if all(q in idx for q in ap): aps.add(frozenset(idx[q] for q in ap))
        z = Fr(B['z']); a = [Fr(x) for x in B['a']]; y = {tuple(map(int, k.split(','))): Fr(v) for k, v in B['y'].items()}
        cong = []
        for cg in B['cong']:
            Ai, Bi = cg['A'], cg['B']
            # check congruence: identical ordered distance matrices
            assert all(D2(pts[Ai[p]], pts[Ai[q]]) == D2(pts[Bi[p]], pts[Bi[q]]) for p in range(len(Ai)) for q in range(len(Ai)))
            cong.append((Ai, Bi, {k: Fr(v) for k, v in cg['c'].items()}))
        nvalid = 0; mn = None
        for s in itertools.product((0, 1), repeat=n):
            if any(s[i] and s[j] for i, j in units): continue
            if any(not any(s[x] for x in ap) for ap in aps): continue
            nvalid += 1
            v = z + sum(a[i] for i in range(n) if s[i]) + sum(c for (i, j), c in y.items() if s[i] and s[j])
            for Ai, Bi, cc in cong:
                v += cc.get(''.join(str(s[x]) for x in Ai), 0) - cc.get(''.join(str(s[x]) for x in Bi), 0)
            mn = v if mn is None else min(mn, v)
        assert mn >= 0, (ci, mn)
        for (i, j), c in y.items(): DD = D2(pts[i], pts[j]); Y[DD] = Y.get(DD, Fr(0)) + c
        Z += z; A += sum(a)
    Ds = sorted(Y); Yf = np.array([float(Y[k]) for k in Ds]); sq = np.sqrt(np.array(Ds, float))
    S = sum(abs(float(Y[k]))/math.sqrt(k) for k in Ds); T = S/float(lam)*1.05 + 1
    M2 = sum(abs(float(Y[k]))*k for k in Ds)/3; step = 2e-4; mx = -1e18; t0 = 0.0
    while t0 < T:
        t = np.arange(t0, min(t0+5, T)+step, step); X = np.outer(t, sq); v = np.where(X > 1e-12, np.sin(X)/np.where(X>0,X,1), 1.0) @ Yf
        mx = max(mx, v.max()); t0 += 5
    ub = mx + M2*step**2/8 + 1e-9; h0 = sum(Y.values())
    assert ub < float(lam) and h0 <= lam
    lo, hi = Fr(C['claimed'][0]), Fr(C['claimed'][1])
    q = lambda x: Z + A*x + h0*x*x + lam*(x - x*x); c2 = h0 - lam; c1 = A + lam; P = [lo, hi]
    if c2 != 0 and lo < -c1/(2*c2) < hi: P.append(-c1/(2*c2))
    assert all(q(p) < 0 for p in P)
    cov.append((lo, hi)); print(f"cert{ci}: {nvalid} valid patterns, C1 min {float(mn):.3g}; max h {mx:.6f} (+{M2*step**2/8:.1e}) < lam {float(lam):.6f}; C3 ok on [{float(lo):.5f},{float(hi):.5f}]", flush=True)
cov.sort(); x = Fr(0)
for lo, hi in cov: assert lo <= x; x = max(x, hi)
assert x >= cap; print(f"INDEPENDENT CHECK PASSED: E^3 -> (l2, l{K}) given delta <= {float(cap)}")
