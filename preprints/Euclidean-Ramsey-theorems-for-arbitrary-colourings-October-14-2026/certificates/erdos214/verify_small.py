"""Rigorous check of Theorem A certificates (arb ball arithmetic + exact rationals).
For k points with a spanning tree whose edges have lengths in (0, D]:
  f(t) = (k-1) phi_D(t) + kappa J0(t) >= -m  for all t >= 0,
  phi_D(t) = J0(Dt) for Dt <= j1 (J0 decreasing on [0,j1]), and >= -RHO_UP for Dt >= j1.
Then sum_tree F >= (k-1+kappa+m) delta^2 - m delta, and Hunter gives 1 <= k delta - sum_tree F.
Checks Q(delta) = (k-1+kappa+m) delta^2 - m delta - k delta + 1 > 0 on [1/k, DMAX] exactly
(for delta < 1/k the union bound k*delta < 1 already contradicts)."""
import sys
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 80
DMAX = Fr(2470, 10000)
RHO_UP = Fr(402760, 10**6)          # -min J0 = 0.4027593957... < 0.402760
J1_LO = Fr(38317, 10**4)             # j_{1,1} = 3.83170597... > 3.8317
def A(x): return arb(x.numerator)/arb(x.denominator)
def J0(x): return x.bessel_j(0)
def J1(x): return x.bessel_j(1)
def check_rho():
    # |J0| min on [0,inf) is at j11; certify J0 >= -RHO_UP: J0(j11) via arb root refinement is standard; check numerically with ball
    j11 = arb('3.8317059702075123156144358863')
    assert (J0(j11) + A(RHO_UP)).lower() > 0
def cells(fun, dfun, M2, lo, hi, bound, depth=60):
    """certify fun(t) >= bound on [lo,hi] using fun(c) - |fun'(c)| r - M2 r^2/2."""
    stack = [(lo, hi)]; n = 0
    while stack:
        a, b = stack.pop(); c = (a+b)/2; r = (b-a)/2
        lb = fun(A(c)) - abs(dfun(A(c)))*A(r) - A(M2)*A(r)*A(r)/2
        if lb.lower() > A(bound).upper(): n += 1; continue
        if r < Fr(1, 10**9): raise AssertionError(f"fails near t={float(c)} lb={lb}")
        stack += [(a, c), (c, b)]
    return n
def verify(k, D, kappa, m):
    D, kappa, m = Fr(D), Fr(kappa), Fr(m)
    assert m >= 0 and k-1+kappa+m >= 0
    # region 1: 0 <= t <= J1_LO/D  (here Dt <= j1, phi = J0(Dt))
    t1 = J1_LO/D
    f = lambda t: (k-1)*J0(A(D)*t) + A(kappa)*J0(t)
    df = lambda t: -(k-1)*A(D)*J1(A(D)*t) - A(kappa)*J1(t)
    M2 = (k-1)*D*D + abs(kappa)            # |J0''| <= 1
    n1 = cells(f, df, M2, Fr(0), t1, -m)
    # the sliver Dt in [J1_LO, j1]: phi >= -RHO_UP anyway (min J0 = -rho), handled in region 2
    # region 2: t >= t1: f >= -(k-1) RHO_UP + kappa J0(t); need kappa J0(t) >= -m + (k-1) RHO_UP
    need = -m + (k-1)*RHO_UP
    assert kappa > 0
    # tail: |J0(t)| <= sqrt(2/(pi t)); choose T with kappa sqrt(2/(pi T)) <= -need
    assert need < 0, "need slack"
    T = max(int(2/3.14159*(float(kappa)/float(-need))**2) + 2, int(t1) + 2)
    assert (A(kappa)*(arb(2)/(arb.pi()*T)).sqrt() + A(need)).upper() < 0
    g = lambda t: A(kappa)*J0(t); dg = lambda t: -A(kappa)*J1(t)
    n2 = cells(g, dg, abs(kappa), t1, Fr(T), need)
    # quadratic in delta, exact
    c2, c1, c0 = k-1+kappa+m, -m-k, Fr(1)
    lo = Fr(1, k); hi = DMAX
    v = -c1/(2*c2); cand = [lo, hi] + ([v] if lo <= v <= hi else [])
    qmin = min(c2*x*x + c1*x + c0 for x in cand)
    assert qmin > 0, f"quadratic fails, min {float(qmin)}"
    return n1, n2, T, float(qmin)
if __name__ == '__main__':
    check_rho()
    # (k, D, kappa, m): certified parameters (found by a separate search, then rounded to rationals)
    out = []
    PARAMS = [(5, Fr(29, 100), Fr(12471, 500), Fr(9041, 1250)),
              (6, Fr(3, 20), Fr(6817, 250), Fr(12829, 2000)),
              (7, Fr(3, 40), Fr(3579, 125), Fr(56751, 10000)),
              (8, Fr(27, 1000), Fr(29193, 1000), Fr(11999, 2500)),
              (9, Fr(1, 500), Fr(29193, 1000), Fr(37599, 10000))]
    for k, D, kap, m in PARAMS:
        try:
            n1, n2, T, q = verify(k, D, kap, m)
            print(f"k={k} D={D} kappa={kap} m={m}: OK  cells {n1}+{n2}, T={T}, min Q = {q:.5f}", flush=True)
        except AssertionError as e:
            print(f"k={k} D={D}: FAILED {e}", flush=True)
