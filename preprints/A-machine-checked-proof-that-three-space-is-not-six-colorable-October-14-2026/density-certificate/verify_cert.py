"""Independent verifier for an m1(R^3) upper-bound certificate (JSON from certify.py).

Run with python-flint (arb ball arithmetic):  <venv-with-flint>/bin/python verify_cert.py cert.json

Statement checked.  Let A be a periodic measurable subset of R^3 of density delta with no two points
at distance 1, f(x) = dens(A ∩ (A - x)) radialised, g = f/delta.  Then
   g(r) = a0 + ∫_(0,∞) Ω(t r) da(t),  Ω(x) = sin(x)/x,  a >= 0,  a0 = delta,  a0 + ∫da = 1,  g(1) = 0,
and for every cut (points x_1..x_N in R^3, coefficients z on pairs (i,i),(i<j)) with
beta := min_{S ⊆ [N]} sum_{(i,j): i,j ∈ S} z_ij  we have  sum z_ij g(|x_i-x_j|) >= beta/delta
(pair marginals of A ∩ (random rigid motion of the points) lie in the correlation polytope).
With nu, y_c >= 0, mu:   G(t) := -nu Ω(t) + sum_c y_c sum_p z_cp Ω(t d_cp).
If (i) mu >= G(0) + 1 and (ii) mu >= G(t) for all t > 0, then integrating against a:
   sum_c y_c beta_c / delta <= a0 G(0) + ∫ G da <= mu - a0,   so delta^2 - mu delta + sum y beta <= 0,
   delta <= (mu + sqrt(mu^2 - 4 sum_c y_c beta_c)) / 2.
Checks: beta_c exactly (rationals); (i) in arb; (ii) by third-order Taylor bounds on cells, using
|Ω'''(x)| <= min(1/4, 1/x + 3/x^2 + 6/x^3 + 6/x^4), and the tail t >= L via |Ω(x)| <= 1/x.
"""
import json, sys, math
from fractions import Fraction
from flint import arb, ctx

ctx.prec = 80
H = lambda s: Fraction(float.fromhex(s))

def load(fn):
    J = json.load(open(fn))
    nu = H(J["nu"]); mu = H(J["mu"])
    cuts = []
    for c in J["cuts"]:
        P = [[H(v) for v in p] for p in c["points"]]
        z = [H(v) for v in c["z"]]
        y = H(c["y"])
        assert y >= 0
        N = len(P)
        pairs = [(i, i) for i in range(N)] + [(i, j) for i in range(N) for j in range(i + 1, N)]
        assert len(pairs) == len(z)
        cuts.append((P, pairs, z, y))
    return J, nu, mu, cuts

def exact_beta(N, pairs, z):
    best = None
    for m in range(1 << N):
        s = sum((zp for (i, j), zp in zip(pairs, z) if (m >> i) & 1 and (m >> j) & 1), Fraction(0))
        if best is None or s < best: best = s
    return best

def main(fn):
    J, nu, mu, cuts = load(fn)
    # exact betas and exact squared distances, merged coefficient list
    terms = {Fraction(1): -nu}      # key: squared distance (exact rational) -> coefficient (exact)
    w0 = Fraction(0); sum_yb = Fraction(0)
    for P, pairs, z, y in cuts:
        N = len(P)
        beta = exact_beta(N, pairs, z)
        assert beta <= 0
        sum_yb += y * beta
        for (i, j), zp in zip(pairs, z):
            q = sum((P[i][k] - P[j][k]) ** 2 for k in range(3))
            if q == 0: w0 += y * zp
            else: terms[q] = terms.get(q, Fraction(0)) + y * zp
    qs = sorted(terms)
    s = [arb(q.numerator).sqrt() / arb(q.denominator).sqrt() for q in qs]
    w = [arb(terms[q].numerator) / terms[q].denominator for q in qs]
    sf = [float(x.mid()) for x in s]; awf = [abs(float(terms[q])) for q in qs]
    w0a = arb(w0.numerator) / w0.denominator
    mua = arb(mu.numerator) / mu.denominator
    print(f"cuts={len(cuts)} distinct distances={len(qs)} w0={float(w0):.10f} mu={float(mu):.10f} sum y*beta={float(sum_yb):.3e}")
    # (i)
    G0 = w0a + sum(w, arb(0))
    assert (mua - G0 - 1) > 0, "a0-column condition fails"
    print("(i) mu - G(0) - 1 =", (mua - G0 - 1).str(5))
    # tail
    margin_inf = float((mua - w0a).lower())
    assert margin_inf > 0, "no slack at infinity"
    Wsum = sum(a / b for a, b in zip(awf, sf)) * (1 + 1e-12)
    L = Wsum / (0.5 * margin_inf)
    print(f"tail: for t >= L = {L:.1f}, G(t) <= w0 + {0.5*margin_inf:.3e} < mu")
    # (ii) on (0, L]: cells [c - h/2, c + h/2]
    def K3(x0):  # sum |w| s^3 sup_{x >= x0 s} |Ω'''(x)|
        tot = 0.0
        for a, b in zip(awf, sf):
            x = x0 * b
            bound = 0.25 if x <= 0 else min(0.25, 1 / x + 3 / x**2 + 6 / x**3 + 6 / x**4)
            tot += a * b**3 * bound
        return tot * (1 + 1e-9)
    t = 0.0; worst = -1e9; worst_t = 0; ncell = 0
    target = 2e-7    # we allow (G upper bound) <= mu - 0 ; cells sized so the cubic remainder <= target/2
    while t < L:
        k3 = K3(t)
        h = (48 * (target / 2) / k3) ** (1 / 3)   # remainder K3 (h/2)^3/6 = K3 h^3/48
        h = min(h, 0.5)
        c = t + h / 2
        ca = arb(c)
        g0 = w0a; g1 = arb(0); g2 = arb(0)
        for si, wi in zip(s, w):
            x = ca * si
            sx, cx = x.sin(), x.cos()
            om = sx / x
            om1 = (x * cx - sx) / (x * x)
            om2 = -sx / x - 2 * cx / (x * x) + 2 * sx / (x * x * x)
            g0 += wi * om; g1 += wi * si * om1; g2 += wi * si * si * om2
        u = h / 2
        # max over |v|<=u of g1 v + g2 v^2/2  <= |g1| u + max(g2,0) u^2/2
        ua = arb(u)
        up1 = g0 + abs(g1) * ua + (g2 if float(g2.upper()) > 0 else arb(0)) * ua ** 2 / 2
        if g2 < 0:      # concave quadratic: global max g0 + g1^2 / (2|g2|) is also an upper bound
            up2 = g0 + g1 * g1 / (2 * abs(g2))
            up1 = up2 if float(up2.upper()) < float(up1.upper()) else up1
        up = up1 + arb(k3 * u ** 3 / 6)
        val = float(up.upper())
        if val > worst: worst, worst_t = val, c
        if not (up < mua):
            raise SystemExit(f"FAIL: G may exceed mu near t={c:.6f}: bound {val:.12f} vs mu {float(mu):.12f}")
        t += h; ncell += 1
        if ncell % 20000 == 0: print(f"   ... t={t:.1f} cells={ncell} worst bound so far {worst:.10f} at {worst_t:.4f}", flush=True)
    print(f"(ii) verified on (0, {L:.1f}] with {ncell} cells; max upper bound {worst:.10f} at t~{worst_t:.4f} < mu")
    sb = arb(sum_yb.numerator) / sum_yb.denominator
    dcert = (mua + (mua * mua - 4 * sb).sqrt()) / 2
    print("CERTIFIED: m1(R^3) <=", dcert.str(12), " upper end", float(dcert.upper()))

if __name__ == "__main__":
    main(sys.argv[1])
