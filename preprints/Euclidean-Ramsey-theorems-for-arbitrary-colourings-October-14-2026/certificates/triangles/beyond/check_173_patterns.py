"""Independent referee checker for '173-pattern-v1' certificates (Erdos #173, pattern-LP with glued copies).

Written from the mathematical definition; shares no code with research/triangles173_beyond/*.py.
Only the JSON op *format* is taken from the certificate (it has to be), and soundness does not depend on
interpreting it the way the author intended: the forbidden triangles are re-derived from the exact geometry.

What a PASS proves (for sides (rho, 1, 1), rho rational in (1/2, 1)):
  (*) there is no translation/rotation-invariant random +-1 colouring sigma of the algebraic plane E whose
      pair correlation is C(r) = a0 + int_(0,inf) J0(r t) dnu(t), a0 >= 0, a0 + |nu| <= 1, and in which
      every triangle with all three sides in F = {rho, 1} is a.s. not monochromatic.
  By Lemma A (C(x)=C(y)=C(z)=-1/3 for the sides of any T-free law) this gives: every red/blue colouring of
  R^2 contains a monochromatic copy of every triangle with algebraic side ratios having two sides in ratio rho.

Checks, all exact unless stated:
  1. Geometry in exact multiquadratic arithmetic Q(sqrt k1, sqrt k2, ...): template triangles placed with exact
     sqrt, rotations (1-m^2, 2m)/(1+m^2) (exact unit complex numbers), reflections = conjugation.
     All points pairwise distinct (exact squared distance != 0).
  2. Forbidden triangles = ALL triples whose three exact squared distances lie in {rho^2, 1} (found by
     enumeration, not read from the certificate). Report whether the ops' intended triangles are among them.
  3. Patterns: all 2^n sign vectors with no monochromatic forbidden triple; L_j = exact min of sum y_pq s_p s_q.
  4. Aux rows: r_i > 0 rational, (possibly degenerate) triangle inequality, sum sg s s >= -1 on all 8 patterns,
     mu >= 0.  Lam = sum L_j - sum mu > 0.
  5. f(t) = sum over exact distinct squared distances D of w_D J0(sqrt(D) t) < Lam on [0, T]:
     python-flint arb; per cell [c-h, c+h]: f(c) (arb point eval) + h * |f'(ball)|, with f' = -sum w d J1(d t)
     evaluated by arb over the whole ball (mean value theorem, rigorous). Adaptive bisection.
  6. Tail t >= T: |J0(x)| <= sqrt(2/(pi x)) for x > 0 (x(J0^2+Y0^2) increases to 2/pi, Watson 13.74), so
     |f(t)| <= sum |w_D| sqrt(2/(pi d T)) < Lam.
usage: check_173_patterns.py cert.json [...]      exit status 0 iff all certificates pass
"""
import sys, json, itertools, time
from fractions import Fraction as Fr
from math import gcd, isqrt
from flint import arb, ctx

ctx.prec = 128


# ---------------------------------------------------------------- exact multiquadratic field arithmetic
def squarefree_split(n):
    """n > 0 integer -> (m, k) with n = m^2 k, k squarefree."""
    m, k, p = 1, 1, 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p; e += 1
        m *= p ** (e // 2)
        if e % 2: k *= p
        p += 1 if p == 2 else 2
    return m, k * n


class Q:
    """element sum_k c_k sqrt(k) over distinct squarefree k >= 1, c_k rational (unique representation)."""
    __slots__ = ('c',)

    def __init__(self, c=None):
        self.c = {k: v for k, v in (c or {}).items() if v != 0}

    @staticmethod
    def rat(x): return Q({1: Fr(x)})

    @staticmethod
    def sqrt_rat(r):
        r = Fr(r); assert r > 0
        m, k = squarefree_split(r.numerator * r.denominator)     # sqrt(p/q) = sqrt(pq)/q
        return Q({k: Fr(m, r.denominator)})

    def __add__(s, o):
        d = dict(s.c)
        for k, v in o.c.items(): d[k] = d.get(k, 0) + v
        return Q(d)

    def __neg__(s): return Q({k: -v for k, v in s.c.items()})
    def __sub__(s, o): return s + (-o)

    def __mul__(s, o):
        d = {}
        for k1, v1 in s.c.items():
            for k2, v2 in o.c.items():
                g = gcd(k1, k2); k = (k1 // g) * (k2 // g)
                d[k] = d.get(k, 0) + v1 * v2 * g
        return Q(d)

    def is_zero(s): return not s.c
    def is_rational(s): return set(s.c) <= {1}
    def ratval(s): return s.c.get(1, Fr(0))
    def key(s): return tuple(sorted(s.c.items()))

    def arb(s):
        return sum((arb(v.numerator) / v.denominator * arb(k).sqrt() for k, v in s.c.items()), arb(0))


ZERO = Q()


class P2:
    """point / complex number x + i y with x, y in Q."""
    __slots__ = ('x', 'y')

    def __init__(self, x, y): self.x, self.y = x, y
    def __add__(s, o): return P2(s.x + o.x, s.y + o.y)
    def __sub__(s, o): return P2(s.x - o.x, s.y - o.y)
    def mul(s, o): return P2(s.x * o.x - s.y * o.y, s.x * o.y + s.y * o.x)
    def conj(s): return P2(s.x, -s.y)
    def norm2(s): return s.x * s.x + s.y * s.y


def template(x, y, z):
    """exact triangle V0=(0,0), V1=(z,0), V2 upper half plane with |V0V1|=z, |V0V2|=y, |V1V2|=x."""
    x, y, z = Fr(x), Fr(y), Fr(z)
    assert x + y > z and y + z > x and x + z > y, "template triangle is degenerate/invalid"
    px = (y * y + z * z - x * x) / (2 * z)
    h2 = y * y - px * px
    assert h2 > 0
    return [P2(ZERO, ZERO), P2(Q.rat(z), ZERO), P2(Q.rat(px), Q.sqrt_rat(h2))]


def unit(m):
    m = Fr(m); d = 1 + m * m
    u = P2(Q.rat((1 - m * m) / d), Q.rat(2 * m / d))
    assert u.norm2().key() == Q.rat(1).key()
    return u


def build(sides, ops):
    a, b, c = sides
    assert ops[0] == ['T'], "first op must place the base triangle"
    pts = template(a, b, c)                      # P0P1 = c, P0P2 = b, P1P2 = a
    intended = [(0, 1, 2)]
    for op in ops[1:]:
        assert op[0] == 'gv' and len(op) == 6, f"unsupported op {op[0]}"
        _, sd, j, refl, v, m = op
        assert j in (0, 1, 2) and 0 <= v < len(pts) and refl in (True, False)
        S = template(*sd)
        if refl: S = [p.conj() for p in S]
        u = unit(m)
        idx = []
        for k in range(3):
            if k == j: idx.append(v)
            else:
                pts.append(pts[v] + (S[k] - S[j]).mul(u)); idx.append(len(pts) - 1)
        intended.append(tuple(sorted(idx)))
    return pts, intended


# ---------------------------------------------------------------- the check
def check(cert, verbose=True, min_rad=Fr(1, 10 ** 9)):
    t0 = time.time()
    assert cert.get('type') == '173-pattern-v1', "wrong certificate type"
    sides = [Fr(s) for s in cert['sides']]
    fam = sorted(set(sides))
    a, b, c = sides
    assert min(sides) > 0 and a + b > c and b + c > a and a + c > b
    fam2 = {(s * s) for s in fam}
    T = Fr(cert['T']); assert T > 0
    W = {}            # exact squared distance key -> [Q sqdist, coefficient]
    Lsum = Fr(0)
    info = []
    for jc, cf in enumerate(cert['configs']):
        pts, intended = build(sides, cf['ops'])
        n = len(pts)
        D = {}
        for p, q in itertools.combinations(range(n), 2):
            d2 = (pts[q] - pts[p]).norm2()
            assert not d2.is_zero(), f"config {jc}: points {p},{q} coincide"
            D[(p, q)] = d2
        is_fam = {pq: d2.is_rational() and d2.ratval() in fam2 for pq, d2 in D.items()}
        forb = [t for t in itertools.combinations(range(n), 3)
                if is_fam[(t[0], t[1])] and is_fam[(t[0], t[2])] and is_fam[(t[1], t[2])]]
        missing = [t for t in intended if t not in forb]
        assert not missing, f"config {jc}: intended triangles {missing} are not exact family triangles"
        y = {}
        for k, v in cf['y'].items():
            p, q = map(int, k.split(',')); assert 0 <= p < q < n and (p, q) not in y
            y[(p, q)] = Fr(v)
        pats = [s for s in itertools.product((1, -1), repeat=n)
                if all(abs(s[i] + s[j] + s[k]) != 3 for i, j, k in forb)]
        assert pats, f"config {jc}: no admissible pattern"
        Lj = min(sum(v * s[p] * s[q] for (p, q), v in y.items()) for s in pats)
        # the same min using only the intended triangles (the certificate's claim); must not exceed ours
        pats_int = [s for s in itertools.product((1, -1), repeat=n)
                    if all(abs(s[i] + s[j] + s[k]) != 3 for i, j, k in intended)]
        Lj_int = min(sum(v * s[p] * s[q] for (p, q), v in y.items()) for s in pats_int)
        Lsum += Lj
        for pq, v in y.items():
            kk = D[pq].key(); W.setdefault(kk, [D[pq], Fr(0)])[1] += v
        nonedge = sum(1 for pq in y if not is_fam[pq])
        info.append((jc, n, len(forb), len(intended), len(pats), Lj, Lj_int, nonedge))
        if verbose:
            print(f"  config {jc}: n={n}, family triangles {len(forb)} (intended {len(intended)}), "
                  f"admissible patterns {len(pats)}, L={float(Lj):.6f} (intended-only L={float(Lj_int):.6f}), "
                  f"weighted non-family pairs {nonedge}")
    musum = Fr(0)
    for X in cert['aux']:
        r = [Fr(v) for v in X['r']]; sg = list(X['sg']); mu = Fr(X['mu'])
        assert len(r) == 3 and len(sg) == 3 and all(z in (1, -1) for z in sg)
        assert mu >= 0 and min(r) > 0
        assert 2 * max(r) <= sum(r), f"aux triple {r} violates the triangle inequality"
        assert all(sg[0] * s0 * s1 + sg[1] * s0 * s2 + sg[2] * s1 * s2 >= -1
                   for s0, s1, s2 in itertools.product((1, -1), repeat=3)), f"aux signs {sg} not valid"
        for rv, z in zip(r, sg):
            d2 = Q.rat(rv * rv); W.setdefault(d2.key(), [d2, Fr(0)])[1] += mu * z
        musum += mu
    Lam = Lsum - musum
    assert Lam > 0, f"Lam = {float(Lam)} <= 0"
    lam = arb(Lam.numerator) / Lam.denominator
    terms = [(d2.arb().sqrt(), arb(w.numerator) / w.denominator) for d2, w in W.values() if w != 0]
    for d, _ in terms: assert d > 0
    # tail
    Ta = arb(T.numerator) / T.denominator
    tail = sum((abs(w) * (2 / (arb.pi() * d * Ta)).sqrt() for d, w in terms), arb(0))
    assert tail < lam, f"tail bound {tail} not below Lam {float(Lam)}"
    # [0, T] by mean-value cells
    stack = [(Fr(k) * T / 4096, Fr(k + 1) * T / 4096) for k in range(4095, -1, -1)]
    cells = 0; worst = None; worst_t = None
    while stack:
        lo, hi = stack.pop()
        cm = (lo + hi) / 2; h = (hi - lo) / 2
        tc = arb(cm.numerator) / cm.denominator
        hb = arb(h.numerator) / h.denominator
        tball = arb(tc.mid(), hb)          # contains [lo, hi] (ball centre/radius exact rationals up to rounding)
        tball = tball.union(arb(lo.numerator) / lo.denominator).union(arb(hi.numerator) / hi.denominator)
        fc = arb(0); fp = arb(0)
        for d, w in terms:
            fc += w * (d * tc).bessel_j(0)
            fp -= w * d * (d * tball).bessel_j(1)
        ub = fc + abs(fp) * hb
        if ub < lam:
            cells += 1
            if worst is None or fc.mid() > worst: worst, worst_t = fc.mid(), cm
            continue
        assert h > min_rad, f"f(t) >= Lam near t = {float(cm)}: f ~ {fc}, Lam = {float(Lam)}"
        stack += [(cm, hi), (lo, cm)]
    if verbose:
        print(f"  Lam = {float(Lam):.12f}; sum L = {float(Lsum):.6f}, sum mu = {float(musum):.6f}")
        print(f"  max f at cell centres ~ {float(worst):.6f} (t ~ {float(worst_t):.4f}); margin {float(Lam) - float(worst):.2e}")
        print(f"  tail(T={float(T)}) <= {float(tail.upper()):.6f}; {len(terms)} distinct distances, {cells} cells, "
              f"{time.time() - t0:.0f}s")
    return Lam, info


if __name__ == "__main__":
    ok = True
    for fn in sys.argv[1:]:
        cert = json.load(open(fn))
        print(f"{fn}: sides {cert['sides']}")
        try:
            check(cert)
            s = sorted(Fr(x) for x in cert['sides'])
            print(f"{fn}: PASS. No invariant J0-correlated law avoids monochromatic triangles with sides in "
                  f"{{{s[0]}, {s[-1]}}}" if len(set(s)) == 2 else f"{fn}: PASS")
        except AssertionError as e:
            ok = False
            print(f"{fn}: FAIL: {e}")
    sys.exit(0 if ok else 1)
