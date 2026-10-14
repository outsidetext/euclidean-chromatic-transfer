"""Independent ball-arithmetic verifier for an upper-bound certificate on m1(R^d), d >= 3.

Usage:  ~/hadwiger-nelson/venv/bin/python verify_rd.py cert.json

THEOREM CHECKED.  Let d >= 3, nu = d/2 - 1, F_b(x) = 0F1(; b; -x^2/4)  (so Omega_d(x) = F_{nu+1}(x)
= Gamma(nu+1)(2/x)^nu J_nu(x) is the spherical average of exp(i x <e, w>)), and for 0 <= j <= (d-1)/2
     h_j(t) = Gamma(nu+1) 2^nu nu^-j t^(j-nu) J_{nu+j}(t) = kappa_j t^(2j) F_{nu+j+1}(t),
     kappa_j = Gamma(nu+1) / ((2 nu)^j Gamma(nu+j+1))          (Davies, arXiv 2610.12301, Lemma 9.2).
Let A subset R^d be measurable with no two points at distance 1 and upper density delta0.  By the
reductions in the proof of Davies' Theorem 8.1 (periodic approximation, compact subset, smoothing),
for every delta < delta0 there is a periodic smooth 0 <= f <= 1 of mean delta whose autocorrelation
vanishes on an annulus around the unit sphere.  Its radialised autocorrelation divided by delta is
     g(r) = a0 + int_(0,inf) Omega_d(t r) da(t),   a0 = delta,  a >= 0,  a0 + a((0,inf)) <= 1,
and (Davies, Lemma 9.2 proof)  a0 [j=0] + int h_j da = 0  for every j above.  Moreover, for points
x_1..x_N in R^d and z on pairs (i,i),(i<j): the vector (E f(y+x_i), E f(y+x_i) f(y+x_j)) is the pair
marginal of independent Bernoulli(f(y+x_i)) variables, hence lies in the correlation polytope; after
averaging over rotations of the configuration and dividing by delta,
     sum_i z_ii + sum_{i<j} z_ij g(|x_i-x_j|) >= beta/delta,   beta = min_{S subset [N]} sum_{i,j in S} z_ij.
(Triangle cuts: z = (+1 at the apex k, +1 on the base pair, -1 on the two sides) give
 1 + g(c) - g(a) - g(b) >= 0 for any a, b, c > 0 with |a-b| <= c <= a+b; beta = 0.)
WEAK DUALITY.  With multipliers c_j (any sign) and y >= 0, put
     G(t) = sum_j c_j h_j(t) + sum_cuts y sum_pairs z Omega_d(t |x_i-x_j|)     (Omega_d(0) = 1).
If  G(0) + 1 <= mu  and  G(t) <= mu for all t > 0, and also  w0 := sum y sum_i z_ii <= mu
(the mass that a((0,inf)) < 1 - a0 may 'lose', at r = 0 only), then integrating,
     sum y beta / delta <= a0 G(0) + int G da + w0 (1 - a0 - |a|) <= mu - delta,
so delta^2 - mu delta + sum y beta <= 0 and delta <= (mu + sqrt(mu^2 - 4 sum y beta)) / 2.

CHECKS (python-flint arb).  beta exactly (Fractions; all data are float64 = dyadic rationals);
G(0) + 1 <= mu; tail t >= L via the explicit Hankel bound (DLMF 10.17(iii), 2nd paragraph: for
nu > -1/2, x > 0, the Hankel expansion of H^(1)_nu terminated at k = l-1 has remainder bounded by the
first neglected term when l >= max(nu - 1/2, 1)), so with |J_nu| <= |H^(1)_nu| on the real line:
     |J_mu(x)| <= sqrt(2/(pi x)) S_mu(x),  S_mu(x) = sum_{k=0}^{l} |a_k(mu)| x^-k,
which gives decreasing bounds for |h_j(t)| (exponent j - nu - 1/2 <= 0) and |Omega_d(x)|;
(0, L]: cells [c-u, c+u] with G(c+v) <= G(c) + G'(c) v + sup_cell G'' v^2/2, where G'' on the cell is
enclosed by evaluating F_b on the ball (arb's rigorous 0F1).
"""
import json, sys, math
from fractions import Fraction
from flint import arb, ctx

ctx.prec = 128
HX = lambda s: Fraction(float.fromhex(s)) if isinstance(s, str) else Fraction(s)
def A(q):
    q = Fraction(q); return arb(q.numerator) / arb(q.denominator)

def exact_beta(N, pairs, z):
    best = None
    for m in range(1 << N):
        s = sum((zp for (i, j), zp in zip(pairs, z) if (m >> i) & 1 and (m >> j) & 1), Fraction(0))
        if best is None or s < best: best = s
    return best

def hankel_a(mu, k):
    """a_k(mu) of DLMF 10.17.1 (exact rational for rational mu)."""
    v = Fraction(1)
    for i in range(1, k + 1):
        v *= (4 * mu * mu - (2 * i - 1) ** 2)
    return v / (math.factorial(k) * 8 ** k)

def S_bound(mu, x):
    """arb upper bound for |J_mu(x)| sqrt(pi x / 2), x > 0 (arb), DLMF 10.17(iii)."""
    l = max(math.ceil(mu - Fraction(1, 2)), 1)
    s = arb(0)
    for k in range(l + 1):
        s += A(abs(hankel_a(mu, k))) / x ** k
    return s

def main(fn):
    J = json.load(open(fn))
    d = int(J["d"]); assert d >= 3
    nu = Fraction(d - 2, 2); Jmax = (d - 1) // 2
    c = [HX(v) for v in J["c"]]; assert 1 <= len(c) <= Jmax + 1
    mu_c = HX(J["mu"])
    # ---- cuts -> merged terms over exact squared distances
    terms = {}; w0 = Fraction(0); sum_yb = Fraction(0); ncut = 0
    for cut in J["cuts"]:
        y = HX(cut["y"]); assert y >= 0
        if cut["kind"] == "tri":
            a, b, cc = [HX(v) for v in cut["abc"]]
            assert a > 0 and b > 0 and cc > 0 and abs(a - b) <= cc <= a + b, "not a triangle"
            lst = [(a * a, -y), (b * b, -y), (cc * cc, y)]; w0 += y
        elif cut["kind"] == "pts":
            P = [[HX(v) for v in p] for p in cut["points"]]; N = len(P)
            assert all(len(p) == d for p in P)
            pairs = [(i, i) for i in range(N)] + [(i, j) for i in range(N) for j in range(i + 1, N)]
            z = [HX(v) for v in cut["z"]]; assert len(z) == len(pairs)
            beta = min(exact_beta(N, pairs, z), Fraction(0))   # beta > 0 may be weakened to 0
            sum_yb += y * beta
            lst = []
            for (i, j), zp in zip(pairs, z):
                q = sum((P[i][k] - P[j][k]) ** 2 for k in range(d))
                if q == 0: w0 += y * zp
                else: lst.append((q, y * zp))
        else:
            raise ValueError(cut["kind"])
        for q, w in lst: terms[q] = terms.get(q, Fraction(0)) + w
        ncut += 1
    qs = sorted(q for q in terms if terms[q] != 0)
    s = [A(q).sqrt() for q in qs]; w = [A(terms[q]) for q in qs]
    ca = [A(v) for v in c]; mu = A(mu_c); w0a = A(w0)
    b0 = A(nu + 1)
    gnu = arb(nu.numerator) / nu.denominator
    kap = [arb.gamma(gnu + 1) / ((2 * gnu) ** j * arb.gamma(gnu + j + 1)) for j in range(len(c))]
    print(f"d={d} derivatives used j=0..{len(c)-1}; cuts={ncut}; distinct distances={len(qs)}; "
          f"w0={float(w0):.6e}; sum y*beta={float(sum_yb):.3e}; mu={float(mu_c):.12g}")
    # ---- (i) a0 column: h_j(0) = [j=0], Omega(0) = 1
    G0 = ca[0] + sum(w, arb(0)) + w0a
    assert G0 + 1 <= mu, "a0 condition fails"
    print("(i)  mu - G(0) - 1 =", (mu - G0 - 1).str(6))
    assert w0a < mu, "no slack at r=0 mass"
    # ---- tail
    pref = arb.gamma(gnu + 1) * arb(2) ** gnu * (2 / arb.pi()).sqrt()
    def tailB(L):
        L = arb(L); tot = arb(0)
        for j, cj in enumerate(ca):
            m = nu + j
            tot += abs(cj) * pref / gnu ** j * L ** (gnu * 0 + j - gnu - arb(1) / 2) * S_bound(m, L)
        for si, wi in zip(s, w):
            x = L * si
            tot += abs(wi) * pref * x ** (-gnu - arb(1) / 2) * S_bound(nu, x)
        return tot
    L = float(J.get("L", 100.0))
    while not (w0a + tailB(L) < mu):
        L *= 1.25
        assert L < 1e8, "tail does not close"
    print(f"(ii) tail: for t >= L = {L:.1f}:  w0 + bound = {(w0a + tailB(L)).str(8)} < mu")
    # ---- (iii) cells on [0, L]:  G(c+v) <= G(c) + G1(c) v + G2(c) v^2/2 + M3 u^3/6,  |v| <= u,
    # with G, G1 = G', G2 = G'' at the point c in arb (tight) and M3 >= sup over the cell of |G'''|:
    #   F_b' = -x/(2b) F_{b+1}  (so F_b^(k) = sum coef x^p F_{b+m}, derived exactly below);
    #   |F_b(x)| <= beta_b(x) := min(1, Gamma(b) 2^(b-1) sqrt(2/pi) x^(1/2-b) S_{b-1}(x)), nonincreasing in x
    #   (|F_b| <= 1: F_b is the characteristic function of a symmetric law on [-1,1] for b >= 1/2;
    #    second bound: DLMF 10.17(iii) Hankel bound above).
    nJ = len(c)
    from math import comb, perm
    def deriv_forms(b, kmax):
        fl = [[(Fraction(1), 0, 0)]]
        for k in range(kmax):
            nxt = {}
            for co, p, m in fl[-1]:
                if p > 0: nxt[(p - 1, m)] = nxt.get((p - 1, m), 0) + co * p
                nxt[(p + 1, m + 1)] = nxt.get((p + 1, m + 1), 0) - co / (2 * (b + m))
            fl.append([(co, p, m) for (p, m), co in nxt.items() if co != 0])
        return fl
    def F(b, x):
        # point evaluation: 0F1 series for small x, Gamma(b)(2/x)^(b-1) J_{b-1}(x) otherwise (both arb-rigorous)
        if x.upper() < 2: return (-(x * x) / 4).hypgeom_0f1(A(b))
        return arb.gamma(A(b)) * (2 / x) ** A(b - 1) * x.bessel_j(A(b - 1))
    def beta_b(b, x):        # upper bound for sup_{y >= x} |F_b(y)|, x float >= 0
        if x <= 0: return arb(1)
        xa = A(Fraction(x))
        Cb = arb.gamma(A(b)) * arb(2) ** A(b - 1) * (2 / arb.pi()).sqrt()
        v = Cb * xa ** (A(Fraction(1, 2) - b)) * S_bound(b - 1, xa)
        return v if v.upper() < 1 else arb(1)
    b0f = nu + 1
    FF = {b0f + j: deriv_forms(b0f + j, 3) for j in range(nJ)}
    def comp_vals(t):
        out = [w0a, arb(0), arb(0)]
        for j in range(nJ):
            b = b0f + j; fm = FF[b]
            Fc = {m: F(b + m, t) for m in range(3)}
            Fd = [sum((A(co) * (t ** p if p else arb(1)) * Fc[m] for co, p, m in fm[k]), arb(0)) for k in range(3)]
            P = [t ** (2 * j - i) * perm(2 * j, i) if 2 * j - i >= 0 else arb(0) for i in range(3)]
            for k in range(3):
                out[k] += ca[j] * kap[j] * sum((comb(k, i) * P[i] * Fd[k - i] for i in range(k + 1)), arb(0))
        fm = FF[b0f]
        for si, wi in zip(s, w):
            x = t * si
            Fc = {m: F(b0f + m, x) for m in range(3)}
            for k in range(3):
                out[k] += wi * si ** k * sum((A(co) * (x ** p if p else arb(1)) * Fc[m] for co, p, m in fm[k]), arb(0))
        return out
    sf = [float(v.upper()) for v in s]; sfl = [float(v.lower()) for v in s]
    def M3(ta, tb):
        tot = arb(0); tbA = A(Fraction(tb))
        for j in range(nJ):
            b = b0f + j; fm = FF[b]
            Fdb = [sum((abs(A(co)) * tbA ** p * beta_b(b + m, ta) for co, p, m in fm[k]), arb(0)) for k in range(4)]
            for i in range(4):
                if 2 * j - i < 0: continue
                tot += abs(ca[j]) * kap[j] * comb(3, i) * perm(2 * j, i) * tbA ** (2 * j - i) * Fdb[3 - i]
        fm = FF[b0f]
        for si, wi, su, sl in zip(s, w, sf, sfl):
            xa, xb = ta * sl * (1 - 1e-15), tb * su * (1 + 1e-15)
            xbA = A(Fraction(xb))
            tot += abs(wi) * A(Fraction(su)) ** 3 * sum((abs(A(co)) * xbA ** p * beta_b(b0f + m, xa) for co, p, m in fm[3]), arb(0))
        return tot
    t = 0.0; u = 1e-3; ncell = 0; worst = -1e300; worst_t = 0.0; fails = 0; nextp = 5000
    while t < L:
        cc_ = t + u
        g0, g1, g2 = comp_vals(A(Fraction(cc_)))
        m3 = M3(t, t + 2 * u)
        ua = A(Fraction(u))
        B = g0 + abs(g1) * ua + (g2 if g2.upper() > 0 else arb(0)) * ua * ua / 2
        if g2.upper() < 0:
            B2 = g0 + g1 * g1 / (2 * abs(g2))
            if B2.upper() < B.upper(): B = B2
        B = B + m3 * ua ** 3 / 6
        if B < mu:
            ub = float(B.upper())
            if ub > worst: worst, worst_t = ub, cc_
            t += 2 * u; ncell += 1
            u = min(u * 1.5, 5.0)
        else:
            u /= 2; fails += 1
            if u < 1e-10:
                raise SystemExit(f"FAIL near t={cc_:.9f}: G bound {float(B.upper()):.15g} vs mu {float(mu_c):.15g}")
        if ncell >= nextp:
            print(f"   ... t={t:.2f} cells={ncell} refinements={fails}", flush=True); nextp += 5000
    print(f"(iii) [0, {L:.1f}] covered by {ncell} cells ({fails} refinements); max upper bound "
          f"{worst:.12g} at t~{worst_t:.5f}; mu = {float(mu_c):.12g}")
    sb = A(sum_yb)
    dcert = (mu + (mu * mu - 4 * sb).sqrt()) / 2
    up = float(dcert.upper())
    print(f"CERTIFIED: m1(R^{d}) <= {dcert.str(12)}  (upper end {up:.12g});  "
          f"1/bound = {1/up:.6f}  =>  chi(R^{d}) >= {math.ceil(1/up - 1e-12)} "
          f"(as an integer bound: chi >= ceil(1/m1); valid if 1/up is not an integer)")

if __name__ == "__main__":
    main(sys.argv[1])
