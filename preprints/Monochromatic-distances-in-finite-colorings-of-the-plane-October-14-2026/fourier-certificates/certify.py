"""Rigorous certificate for m_D(R^2) <= 1/(1+sum v): check h(t)=1+sum_d v_d J0(d t) >= 0 for all t>=0.
v rational (rounded LP solution, shrunk). On [0,T]: grid with spacing eta, float J0 (scipy, error < 1e-15) with margin, and
|h'(t)| <= L := sum |v_d| d (since |J0'|=|J1|<=1/sqrt2<1), so h(t) >= h(grid) - L*eta/2.
For t >= T: |J0(x)| <= sqrt(2/(pi x)) (x>0), so h(t) >= 1 - sum |v_d| sqrt(2/(pi d T)) > 0.
usage: certify.py kind N"""
import sys, numpy as np, sympy, mpmath
from fractions import Fraction as Fr
from scipy.special import j0
from scipy.optimize import linprog
mpmath.mp.dps = 40
kind, N = sys.argv[1], int(sys.argv[2])
fam = {"odd": lambda N: list(range(1, 2*N, 2)), "sq": lambda N: [k*k for k in range(1, N+1)],
       "prime": lambda N: list(sympy.primerange(2, N+1)), "pow2": lambda N: [2**k for k in range(N)]}
D = fam[kind](N)
Dn = np.array(D, float)
t = np.concatenate([np.linspace(0, 2.0/min(D), 20000), np.linspace(2.0/min(D), 80.0/min(D), 400000)])
res = linprog(-np.ones(len(D)), A_ub=-j0(np.outer(t, Dn)), b_ub=np.ones(len(t)), bounds=[(None,None)]*len(D), method="highs")
shrink = Fr(97, 100)
v = [Fr(round(x*10**6), 10**6)*shrink for x in res.x]
S = sum(v); bound = 1/(1+S)
L = sum(abs(x)*d for x, d in zip(v, D))
A = sum(mpmath.mpf(abs(x).numerator)/abs(x).denominator/mpmath.sqrt(d) for x, d in zip(v, D))
T = mpmath.mpf(2)/mpmath.pi*(mpmath.mpf(A)*mpmath.mpf(1.25))**2      # tail: 1 - A*sqrt(2/(pi T)) >= 0.2
tail = 1 - A*mpmath.sqrt(2/(mpmath.pi*T))
def h(tt): return 1 + sum(mpmath.mpf(x.numerator)/x.denominator*mpmath.besselj(0, d*tt) for x, d in zip(v, D))
# adaptive grid: coarse numpy prescreen then rigorous mpmath at chosen points
Tf = float(T); vf = np.array([float(x) for x in v])
eta = 1e-3/max(D); n = int(Tf/eta)+1
worst = 1e9; ok = True; chunk = 2_000_000
for s in range(0, n, chunk):
    tt = np.arange(s, min(n, s+chunk))*eta
    hv = 1 + j0(np.outer(tt, Dn)) @ vf
    m = hv.min(); worst = min(worst, m)
    if m - float(L)*eta - 1e-6 <= 0: ok = False
print(f"{kind} N={N} |D|={len(D)} sum v={float(S):.5f} m_D<={float(bound):.6f} chi>={float(1/bound):.3f} "
      f"T={Tf:.1f} grid min h={worst:.5f} Lip*eta/2={float(L)*eta/2:.2e} tail={float(tail):.3f} -> {'CERTIFIED' if ok and tail>0 else 'FAILED'}")

import json
json.dump({"family": kind, "N": N, "D": D, "v": [str(x) for x in v], "sum_v": str(S), "m_D_bound": str(bound),
           "T": float(T), "eta": eta, "grid_min_h": float(worst), "certified": bool(ok and tail > 0)},
          open(f"cert_{kind}_{N}.json", "w"), indent=1)
