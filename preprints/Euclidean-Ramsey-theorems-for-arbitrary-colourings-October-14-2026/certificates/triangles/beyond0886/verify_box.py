"""Independent rigorous verifier for BOX certificates (Erdos #173, 2-colourings).

A box certificate covers every triangle with sides (a, b, 1), a in [a0,a1], b in [b0,b1] (algebraic a, b;
triangle inequality a + b >= 1 assumed, degenerate allowed), with ONE dual certificate:
  y = (y_a, y_b, y_c) weights on the pairs of T of length a, b, 1;  L := min over the non-monochromatic
  patterns of T of sum y s s = min_i (y_i - y_j - y_k)  (exactly one pair agrees);
  aux triangles (r1,r2,r3) rational, signs sg (sum sg s s >= -1 for all +-1 patterns, checked), mu >= 0;
  Lam := L - sum mu > 0, and for all t >= 0 and all (a,b) in the box
      f(t;a,b) = y_a J0(a t) + y_b J0(b t) + y_c J0(t) + sum_aux mu sum sg J0(r t)  <  Lam.
Soundness exactly as in verify173.py (spectral measure G of mass <= 1:  Lam <= int f dG <= max(0, sup f)).
Check: t-cells; fixed (aux + side 1) part by second-order Taylor in Arb; the a- and b-terms by second-order Taylor
enclosures of J0 on the interval [a0 t_lo, a1 t_hi]; tail t >= T by |J0(x)| <= sqrt(2/(pi x)).
usage: verify_box.py certs.json   (a JSON list of box certificates; also prints the union of boxes)
"""
import sys, json, itertools
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 64

def A(x): return arb(x.numerator) / arb(x.denominator)
def ball(lo, hi): return (A(lo) + A(hi)) / 2 + arb(0, float(hi - lo) / 2 * (1 + 1e-12) + 1e-30)  # encloses [lo,hi]
J0MIN = A(Fr(-402760, 10**6))     # min J0 = -0.4027593957... > -0.402760
def j0_range(lo, hi):
    """(lower, upper) arb bounds of J0 on [lo, hi], 0 <= lo <= hi: second-order Taylor about the midpoint m
    (J0' = -J1, |J0''| <= 1): J0 in J0(m) +- (|J1(m)| rho + rho^2/2), intersected with J0MIN <= J0 <= 1 and
    |J0(x)| <= sqrt(2/(pi x))."""
    m = A((lo + hi) / 2); rho = A((hi - lo) / 2)
    e = m.bessel_j(0); d = abs(m.bessel_j(1)) * rho + rho * rho / 2
    lb = arb((e - d).lower()); ub = arb((e + d).upper())
    lb = lb if lb > J0MIN else J0MIN; ub = ub if ub < 1 else arb(1)
    if lo > 0:
        B = (2 / (arb.pi() * A(lo))).sqrt()
        if (-B) > lb: lb = -B
        if B < ub: ub = B
    return lb, ub
W = Fr(1, 64); PIECE = {}
def piece(k):
    """rigorous (lb, ub) of J0 on [kW, (k+1)W] (cached; exact-point arbs)."""
    if k not in PIECE: PIECE[k] = j0_range(k * W, (k + 1) * W)
    return PIECE[k]
def j0_range_wide(lo, hi):
    """(lower, upper) bounds of J0 on [lo, hi]: Taylor if narrow, else min/max over the cached W-pieces covering
    [lo, hi] (the pieces [kW,(k+1)W], k0 <= k <= k1, cover [lo, hi]), intersected with the envelope bound."""
    if hi - lo <= 2 * W: return j0_range(lo, hi)
    k0 = (lo / W).__floor__(); k1 = (hi / W).__ceil__() - 1
    lb, ub = piece(k0)
    for k in range(k0 + 1, k1 + 1):
        l, u = piece(k)
        if l < lb: lb = l
        if u > ub: ub = u
    if lo > 0:
        B = (2 / (arb.pi() * A(lo))).sqrt(); Bl = arb(B.upper())
        if (-Bl) > lb: lb = -Bl
        if Bl < ub: ub = Bl
    return lb, ub
def term_ub(y, lo, hi):
    lb, ub = j0_range_wide(lo, hi)
    return A(y) * (ub if y >= 0 else lb)

def verify_box(Cj, minrad=Fr(1, 10**6)):
    (a0, a1), (b0, b1) = [[Fr(x) for x in iv] for iv in Cj['box']]
    assert 0 < a0 <= a1 and 0 < b0 <= b1
    y = [Fr(x) for x in Cj['y']]
    L = min(y[i] - y[(i+1) % 3] - y[(i+2) % 3] for i in range(3))
    mut = Fr(0); fixed = {Fr(1): y[2]}
    for X in Cj['aux']:
        r = [Fr(x) for x in X['r']]; sg = X['sg']; mu = Fr(X['mu'])
        assert all(v > 0 for v in r) and mu >= 0 and all(z in (1, -1) for z in sg)
        assert r[0] <= r[1] + r[2] and r[1] <= r[0] + r[2] and r[2] <= r[0] + r[1]
        assert min(sg[0]*s[0]*s[1] + sg[1]*s[0]*s[2] + sg[2]*s[1]*s[2] for s in itertools.product((1, -1), repeat=3)) >= -1
        for v, z in zip(r, sg): fixed[v] = fixed.get(v, Fr(0)) + mu * z
        mut += mu
    Lam = L - mut; assert Lam > 0, "Lam <= 0"
    lam = A(Lam); T = Fr(Cj['T'])
    keys = [k for k in fixed if fixed[k] != 0]; ck = {k: A(fixed[k]) for k in keys}; rk = {k: A(k) for k in keys}
    tail = sum((abs(ck[k]) * (2 / (arb.pi() * rk[k] * A(T))).sqrt() for k in keys), arb(0))
    tail += abs(A(y[0])) * (2 / (arb.pi() * A(a0) * A(T))).sqrt() + abs(A(y[1])) * (2 / (arb.pi() * A(b0) * A(T))).sqrt()
    assert tail.upper() < lam.lower(), f"tail {tail} >= Lam {float(Lam)}"
    M2 = sum((abs(ck[k]) * rk[k] * rk[k] for k in keys), arb(0))
    stack = [(Fr(0), T)]; cells = 0
    while stack:
        lo, hi = stack.pop(); c = (lo + hi) / 2; rad = (hi - lo) / 2
        x = A(c); ra = A(rad)
        h = arb(0); hp = arb(0)
        for k in keys:
            z = x * rk[k]; h += ck[k] * z.bessel_j(0); hp += ck[k] * rk[k] * z.bessel_j(1)
        ub = h + abs(hp) * ra + M2 * ra * ra / 2
        ub += term_ub(y[0], a0 * lo, a1 * hi) + term_ub(y[1], b0 * lo, b1 * hi)
        if ub.upper() < lam.lower(): cells += 1; continue
        if rad < minrad: raise AssertionError(f"box {Cj['box']}: fails near t={float(c)} ub={ub} Lam={float(Lam)}")
        stack += [(lo, c), (c, hi)]
    return Lam, cells

def check_j0min():
    """Rigorous: J0(x) > J0MIN for all x >= 0 (cells on [0,20] by Taylor; x >= 20: |J0| <= sqrt(2/(pi x)) < 0.18)."""
    stack = [(Fr(0), Fr(20))]
    while stack:
        lo, hi = stack.pop()
        m = A((lo + hi) / 2); rho = A((hi - lo) / 2)
        lb = m.bessel_j(0) - abs(m.bessel_j(1)) * rho - rho * rho / 2
        if lb > J0MIN: continue
        assert hi - lo > Fr(1, 10**9), "J0MIN check failed"
        stack += [(lo, (lo + hi) / 2), ((lo + hi) / 2, hi)]
    assert (2 / (arb.pi() * 20)).sqrt() < 0.18
    print("J0 >= -0.402760 on [0,inf): verified")

if __name__ == "__main__":
    check_j0min()
    certs = json.load(open(sys.argv[1])); boxes = []
    for i, Cj in enumerate(certs):
        Lam, cells = verify_box(Cj); boxes.append(Cj['box'])
        print(f"box {i}: a in [{float(Fr(Cj['box'][0][0])):.4f},{float(Fr(Cj['box'][0][1])):.4f}] b in [{float(Fr(Cj['box'][1][0])):.4f},{float(Fr(Cj['box'][1][1])):.4f}]  Lam={float(Lam):.4f}  {len(Cj['aux'])} aux  {cells} t-cells  OK", flush=True)
    print(f"ALL {len(certs)} BOX CERTIFICATES VERIFIED")
