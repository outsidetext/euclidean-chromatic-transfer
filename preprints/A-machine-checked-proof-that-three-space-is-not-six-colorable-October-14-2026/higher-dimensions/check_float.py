# Independent float re-check (Claude) of m1rd certificates incl. general point cuts:
# G(t) = sum_j c_j h_j(t) + sum_cuts y sum_pairs z Om_d(t|xi-xj|) <= mu (t>0), G(0)+1 <= mu, w0 <= mu,
# bound delta <= (mu + sqrt(mu^2 - 4 sum y beta))/2, beta = min(0, min_S sum_{i,j in S} z_ij).
import json, sys, itertools, numpy as np
from scipy.special import jv, gamma
hx = lambda s: float.fromhex(s) if isinstance(s, str) else float(s)
for fn in sys.argv[1:]:
    J = json.load(open(fn)); d = int(J['d']); nu = d/2 - 1
    c = [hx(v) for v in J['c']]; mu = hx(J['mu'])
    def Om(x):
        x = np.asarray(x, float); out = np.ones_like(x); m = x > 1e-12
        out[m] = gamma(nu+1)*(2/x[m])**nu*jv(nu, x[m]); return out
    def h(j, t):
        b = nu + j + 1; kap = gamma(nu+1)/((2*nu)**j*gamma(nu+j+1)); t = np.asarray(t, float)
        F = np.ones_like(t); m = t > 1e-12; F[m] = gamma(b)*(2/t[m])**(b-1)*jv(b-1, t[m]); return kap*t**(2*j)*F
    terms = {}; w0 = 0.0; syb = 0.0
    for cu in J['cuts']:
        y = hx(cu['y'])
        if cu['kind'] == 'tri':
            a, b, cc = [hx(v) for v in cu['abc']]; assert abs(a-b) <= cc <= a+b
            for q, w in ((a, -y), (b, -y), (cc, y)): terms[q] = terms.get(q, 0) + w
            w0 += y
        else:
            P = np.array([[hx(v) for v in p] for p in (cu['points'] if isinstance(cu['points'], list) else eval(cu['points']))])
            z = [hx(v) for v in (cu['z'] if isinstance(cu['z'], list) else eval(cu['z']))]; N = len(P)
            pairs = [(i, i) for i in range(N)] + [(i, j) for i in range(N) for j in range(i+1, N)]
            beta = min(0.0, min(sum(zp for (i, j), zp in zip(pairs, z) if (m >> i) & 1 and (m >> j) & 1) for m in range(1 << N)))
            syb += y*beta
            for (i, j), zp in zip(pairs, z):
                if i == j: w0 += y*zp
                else:
                    q = float(np.linalg.norm(P[i]-P[j])); terms[q] = terms.get(q, 0) + y*zp
    qs = np.array(sorted(terms)); ws = np.array([terms[q] for q in qs])
    def G(t): return sum(cj*h(j, t) for j, cj in enumerate(c)) + Om(np.outer(t, qs)).reshape(len(t), -1) @ ws + w0
    G0 = G(np.array([0.0]))[0]; L = 400.0; t = np.arange(1e-6, L, 2e-4); g = G(t); i = g.argmax()
    bound = (mu + np.sqrt(mu*mu - 4*syb))/2
    print(f"{fn.split('/')[-1]}: d={d} mu={mu:.10g} G(0)+1-mu={G0+1-mu:.2e} w0<=mu:{w0<=mu} max G-mu={g[i]-mu:.2e} at t={t[i]:.2f} "
          f"sum y beta={syb:.2e} => m1 <= {bound:.10g}, chi >= {int(np.ceil(1/bound))}")
