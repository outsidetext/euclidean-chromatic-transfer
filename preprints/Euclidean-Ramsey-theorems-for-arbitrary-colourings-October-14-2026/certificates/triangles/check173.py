# Independent check (Claude) of 2-colour triangle certificates: recompute L_j by brute force, check aux inequalities,
# and check f(t) < Lam on a fine grid (second-order bound, |J0''| <= 1) plus tail |J0(x)| <= sqrt(2/(pi x)).
import json, sys, itertools, math, numpy as np
from fractions import Fraction as Fr
from scipy.special import j0
for fn in sys.argv[1:]:
    d = json.load(open(fn)); ev = lambda x: eval(x) if isinstance(x, str) else x
    S2 = [Fr(x) for x in ev(d['sides2'])]; G = [Fr(x) for x in ev(d['gram'])]
    q = lambda m, n: G[0]*m*m + 2*G[1]*m*n + G[2]*n*n     # squared length of m u + n v
    terms = {}; Ltot = Fr(0)
    for cf in ev(d['configs']):
        P = [tuple(p) for p in cf['points']]; N = len(P)
        D2 = {(i, j): q(P[i][0]-P[j][0], P[i][1]-P[j][1]) for i in range(N) for j in range(i+1, N)}
        trip = [t for t in itertools.combinations(range(N), 3) if sorted(D2[(a, b)] for a, b in itertools.combinations(t, 2)) == sorted(S2)]
        y = {tuple(map(int, k.split(','))): Fr(v) for k, v in cf['y'].items()}
        L = None
        for s in itertools.product((1, -1), repeat=N):
            if any(s[a] == s[b] == s[c] for a, b, c in trip): continue
            v = sum(w*s[i]*s[j] for (i, j), w in y.items()); L = v if L is None else min(L, v)
        Ltot += L
        for (i, j), w in y.items(): terms[D2[(i, j)]] = terms.get(D2[(i, j)], 0) + w
    mus = Fr(0)
    for ax in ev(d['aux']):
        r = [Fr(x) for x in ax['r']]; sg = ax['sg']; mu = Fr(ax['mu']); assert mu >= 0
        a, b, c = sorted(r); assert c <= a + b        # realizable (possibly degenerate) triangle
        # sum sg_i s s >= -1 for all +-1 patterns: pairs (01),(02),(12) with signs sg
        assert all(sg[0]*x*y_ + sg[1]*x*z + sg[2]*y_*z >= -1 for x, y_, z in itertools.product((1, -1), repeat=3))
        # pairs: r[0] ~ (0,1), r[1] ~ (0,2), r[2] ~ (1,2) ; lengths (not squared)
        for rr, sgi in zip(r, sg): terms[rr*rr] = terms.get(rr*rr, 0) + mu*sgi
        mus += mu
    Lam = Ltot - mus; assert Lam > 0
    ds = np.array([math.sqrt(float(k)) for k in terms]); cs = np.array([float(v) for v in terms.values()])
    T = float(ev(d['T'])); step = 1e-4; t = np.arange(0, T + step, step); f = j0(np.outer(t, ds)) @ cs
    M2 = float(sum(abs(c)*dd*dd for c, dd in zip(cs, ds))); ub = f.max() + M2*step**2/8
    tail = sum(abs(c)*math.sqrt(2/(math.pi*dd*T)) for c, dd in zip(cs, ds))
    ok = ub < float(Lam) and tail < float(Lam)
    print(f"{fn}: sides^2={[str(x) for x in S2]} Lam={float(Lam):.6f} max f={f.max():.5f} (+{M2*step**2/8:.1e}) tail={tail:.4f} -> {'OK' if ok else 'FAIL'}")
