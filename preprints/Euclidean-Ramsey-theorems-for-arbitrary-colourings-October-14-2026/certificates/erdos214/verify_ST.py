"""Rigorous check of Theorem B+ (S+T certificate): every 5-point S with algebraic distances, all >= R0, has a red copy.
usage: verify_ST.py cert.json R0 tstar [DMAX, default 0.2470; use 0.2873 >= rho/(1+rho) for the m1-free version]
Inequalities (expectations under the transfer measure):
 (ST) 0 <= alpha*E[M] - 1 - cs*E[Ps] - cd*E[Pd]  [alpha M - 1 - cs Ps - cd Pd >= 0 on all admissible patterns of S+T]
      E[M]=15 delta, E[Ps]=3 sum_{i<j}F(r_ij), E[Pd]=sum_{i<j} sum_{v!=v'} F(|s_i+v-s_j-v'|)
 (Q)  0 <= z0 + delta sum a + sum_e y_e F(d_e)    [spindle]
 (F1) kappa F(1) = 0
 S-part(t) <= 7.5 cs + 15 cd J0(t)  (PD for S and for the 15 distinct points of S+T; cs >= cd >= 0)
 S-part(t) <= 30 cs sqrt(2/(pi R0 t)) + 60 cd sqrt(2/(pi (R0-1) t))   (cross distances >= R0-1)"""
import json, sys, itertools
from fractions import Fraction as Fr
from itertools import combinations
from flint import arb, ctx
ctx.prec = 100
C = json.load(open(sys.argv[1])); R0 = Fr(sys.argv[2]); TS = Fr(sys.argv[3])
DMAX = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(2470, 10000)
if DMAX >= Fr(2872, 10000):  # Delsarte: F(1)=0, a0>=delta^2 => delta <= rho/(1+rho) < 0.28713 (rho < 0.402760)
    assert Fr(402760, 10**6)/(1+Fr(402760, 10**6)) < DMAX
A = lambda x: arb(x.numerator)/arb(x.denominator)
al, cs, cd, z0, kap, lam = (Fr(C[k]) for k in ['alpha', 'cs', 'cd', 'z0', 'kappa', 'lam'])
a = [Fr(v) for v in C['a']]; y = [Fr(v) for v in C['y']]; pairs = [tuple(p) for p in C['pairs']]
assert R0 > 2 and cs >= cd >= 0 and lam >= 0
# (1) S+T pattern inequality: enumerate all X:[5]->{none,0,1,w} hitting all three copies (cross pairs are at
# distance >= R0-1 > 1, so the only unit pairs are inside each s_i+T, allowing <= 1 blue per triangle)
worst = None
for X in itertools.product(range(4), repeat=5):
    if not {1, 2, 3} <= set(X): continue
    M = sum(x > 0 for x in X)
    Ps = sum(1 for i, j in combinations(range(5), 2) if X[i] and X[i] == X[j])
    Pd = sum(1 for i, j in combinations(range(5), 2) if X[i] and X[j] and X[i] != X[j])
    v = al*M - 1 - cs*Ps - cd*Pd
    worst = v if worst is None else min(worst, v)
assert worst >= 0, worst
print(f"(1) S+T inequality >= 0 on all admissible patterns (min {float(worst):.3e})")
# (2) spindle
unit = [(0,1),(0,2),(1,2),(1,3),(2,3),(0,4),(0,5),(4,5),(4,6),(5,6),(3,6)]
ind = [S for r in range(8) for S in combinations(range(7), r) if not any(i in S and j in S for i, j in unit)]
qmin = min(z0 + sum(a[i] for i in S) + sum(y[k] for k, (i, j) in enumerate(pairs) if i in S and j in S) for S in ind)
assert qmin >= 0, qmin
print(f"(2) spindle q >= 0 on {len(ind)} independent sets (min {float(qmin):.3e})")
# exact spindle geometry
s3, s11 = arb(3).sqrt(), arb(11).sqrt(); sq = lambda x: x*x
base = [(arb(0), arb(0)), (arb(1), arb(0)), (arb(1)/2, s3/2), (arb(3)/2, s3/2)]
c, s = arb(5)/6, s11/6; rot = lambda p: (c*p[0]-s*p[1], s*p[0]+c*p[1])
P = base + [rot(base[1]), rot(base[2]), rot(base[3])]
d2 = lambda i, j: sq(P[i][0]-P[j][0]) + sq(P[i][1]-P[j][1])
for i, j in unit: assert abs(d2(i, j)-1).upper() < 1e-25
d = [d2(i, j).sqrt() for i, j in pairs]
# (3) B <= lam
Y = sum(y); B = -30*cs - 60*cd + Y + kap
assert B <= lam
print(f"(3) lam = {float(lam):.5f}, B = {float(B):.5f} <= lam")
# (4) H bound
ya = [A(v) for v in y]; ka = A(kap); la = A(lam); csa, cda = A(cs), A(cd)
nz = [k for k in range(len(y)) if y[k] != 0]
def g(t): return sum((ya[k]*(d[k]*t).bessel_j(0) for k in nz), arb(0)) + ka*t.bessel_j(0)
def dg(t): return -sum((ya[k]*d[k]*(d[k]*t).bessel_j(1) for k in nz), arb(0)) - ka*t.bessel_j(1)
M2g = sum((abs(ya[k])*d[k]*d[k] for k in nz), arb(0)) + abs(ka)
def amp(t): return 30*csa*(2/(arb.pi()*A(R0)*t)).sqrt() + 60*cda*(2/(arb.pi()*A(R0-1)*t)).sqrt()
def cells(f, df, M2, lo, hi, extra):
    st = [(lo, hi)]; n = 0
    while st:
        p, q = st.pop(); m = (p+q)/2; r = (q-p)/2
        ub = f(A(m)) + abs(df(A(m)))*A(r) + M2*A(r)*A(r)/2 + extra(p)
        if (ub - la).upper() < 0: n += 1; continue
        if r < Fr(1, 10**8): raise AssertionError(f"(4) fails near t={float(m)}")
        st += [(p, m), (m, q)]
    return n
# region [0, TS]: g + 7.5cs + 15cd J0
f1 = lambda t: g(t) + 15*cda*t.bessel_j(0); df1 = lambda t: dg(t) - 15*cda*t.bessel_j(1)
n1 = cells(f1, df1, M2g + 15*cda, Fr(0), TS, lambda p: 7.5*csa)
# region [TS, T]: g + amp(lo)
env = sum((abs(ya[k])/d[k].sqrt() for k in nz), arb(0)) + abs(ka)
T = 64
while (env*(2/(arb.pi()*T)).sqrt() + amp(arb(T)) - la).upper() >= 0: T *= 2
n2 = cells(g, dg, M2g, TS, Fr(T), lambda p: amp(A(p)))
print(f"(4) H(t) <= lam on (0,{TS}] ({n1} cells, PD bound) and ({TS},{T}] ({n2} cells, decay bound) + tail; R0 = {R0}")
# (5) quadratic
c2 = B - lam; c1 = 15*al + sum(a) + lam; c0 = -1 + z0
cand = [Fr(0), DMAX] + ([-c1/(2*c2)] if c2 != 0 and 0 <= -c1/(2*c2) <= DMAX else [])
pmax = max(c2*x*x + c1*x + c0 for x in cand)
assert pmax < 0, float(pmax)
print(f"(5) P(delta) = {float(c2):.4f} d^2 + {float(c1):.4f} d + {float(c0):.6f} < 0 on [0, {float(DMAX)}] (max {float(pmax):.5f})")
print("ALL CHECKS PASSED")
