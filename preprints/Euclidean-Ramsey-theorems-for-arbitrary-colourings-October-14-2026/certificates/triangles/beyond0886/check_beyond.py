"""INDEPENDENT checker for '173-pattern-v1' certificates (Erdos #173, 2-colourings, triangle with sides a,b,c).
Shares no code with the generator (gencert.py / core.py / confgen.py).

Claim: every red/blue colouring of R^2 has a monochromatic congruent copy of T = (a, b, c) (rational sides).

Soundness.  Suppose a colouring has no monochromatic copy of T.  Folner averaging over E x| K (E = algebraic
plane, K = algebraic rotations) and colour-swap symmetrisation give an invariant random +-1 colouring sigma of E,
a.s. without monochromatic algebraic copies of T, with E sigma(x)sigma(y) = C(|x-y|) = int J0(|x-y| t) dG(t),
G >= 0, G[0,inf) <= 1 (OpenAI Thm 2.3 + transfer, as in verify173.py).
Lemma A: equilateral triangles give 3C(s) >= -1 for s in {a,b,c}; T gives C(a)+C(b)+C(c) = -1; hence
C(a)=C(b)=C(c)=-1/3 and every triangle with all three sides in {a,b,c} ('family triangle') has
E[sum of its 3 pair products] = -1 = the minimum over +-1 patterns, so it is a.s. NOT monochromatic.
Configurations: each is built from T by ops that place family triangles by exact rigid motions with rational
Pythagorean rotations (cos, sin rational), so all points are algebraic and each constructed triangle is an exact
family triangle.  For config j with pair weights y^j: L_j := min over +-1 patterns (s_0 = +1; energies are even)
with no constructed triangle monochromatic of sum y_ab s_a s_b  (computed here exactly).  Aux triangles
(rational sides, triangle inequality, signs sg with sum sg s s >= -1 for every pattern), weights mu >= 0.
Then sum_j L_j - sum mu <= E[...] = int f dG <= max(0, sup f),  f(t) = sum_j sum_ab y_ab J0(d_ab t) +
sum_k mu_k sum_i sg_i J0(r_i t).  The checker verifies Lam := sum L_j - sum mu > 0 and f(t) < Lam for all
t >= 0 (arb balls, adaptive cells on [0,T] with second-order Taylor bound |d^2/dt^2 J0(r t)| <= r^2; tail
t >= T via |J0(x)| <= sqrt(2/(pi x))).  Contradiction => the colouring has a monochromatic copy of T.
usage: check_beyond.py cert.json [...]
"""
import sys, json, itertools, time
from fractions import Fraction as Fr
from flint import arb, acb, ctx
ctx.prec = 96

def A(q): q = Fr(q); return arb(q.numerator) / arb(q.denominator)

def replay(sides, ops):
    """arb coordinates of the configuration + list of constructed triangles + exact edge lengths."""
    a, b, c = sides; fam = set(sides)
    # T: P0 = 0, P1 = c, P2 with |P0P2| = b, |P1P2| = a
    def place(x, y, z):
        # triangle with |V0V1| = z, |V0V2| = y, |V1V2| = x ; strict triangle inequality required
        assert x + y > z and x + z > y and y + z > x, "degenerate/invalid family triangle"
        px = (A(y) ** 2 + A(z) ** 2 - A(x) ** 2) / (2 * A(z)); h = (A(y) ** 2 - px ** 2).sqrt()
        return [acb(0), acb(A(z)), acb(px, h)]
    assert ops[0] == ['T']
    P = place(a, b, c); tris = [(0, 1, 2)]; E = {(0, 1): c, (0, 2): b, (1, 2): a}
    for op in ops[1:]:
        if op[0] == 'gv':
            _, sd, j, refl, v, m = op
            x, y, z = [Fr(s) for s in sd]
            assert x in fam and y in fam and z in fam, "glued triangle is not a family triangle"
            S = place(x, y, z)
            if refl: S = [s.conjugate() for s in S]
            m = Fr(m); rotc = acb(A((1 - m * m) / (1 + m * m)), A(2 * m / (1 + m * m)))   # |rotc| = 1 exactly
            assert 0 <= v < len(P)
            idx = []
            for k in range(3):
                if k == j: idx.append(v)
                else: P.append(P[v] + (S[k] - S[j]) * rotc); idx.append(len(P) - 1)
            L = {(0, 1): z, (0, 2): y, (1, 2): x}
            for (p, q), l in L.items(): E[(min(idx[p], idx[q]), max(idx[p], idx[q]))] = l
        elif op[0] == 'ge':
            _, i, k, x, y, side = op; x, y = Fr(x), Fr(y)
            e = E[(min(i, k), max(i, k))]                       # must be an exact constructed edge
            assert x in fam and y in fam and e in fam and x + y > e and x + e > y and y + e > x
            u = (P[k] - P[i]) / A(e)
            px = (A(x) ** 2 - A(y) ** 2 + A(e) ** 2) / (2 * A(e)); h = (A(x) ** 2 - px ** 2).sqrt()
            assert side in (1, -1)
            P.append(P[i] + u * acb(px, side * h)); n = len(P) - 1; idx = [i, k, n]
            E[(min(i, n), max(i, n))] = x; E[(min(k, n), max(k, n))] = y
        else: raise AssertionError("unknown op")
        tris.append(tuple(sorted(idx)))
    return P, tris, E

def patterns(n, tris):
    by = {}
    for t in tris: by.setdefault(max(t), []).append(t)
    out = []; s = [1] + [0] * (n - 1)
    def rec(i):
        if i == n: out.append(tuple(s)); return
        for v in (1, -1):
            s[i] = v
            if all(abs(s[p] + s[q] + s[r]) != 3 for (p, q, r) in by.get(i, [])): rec(i + 1)
        s[i] = 0
    rec(1); return out

def check(cert, verbose=True):
    t0 = time.time()
    assert cert['type'] == '173-pattern-v1'
    sides = [Fr(s) for s in cert['sides']]; a, b, c = sides
    assert min(sides) > 0 and a + b > c and a + c > b and b + c > a
    T = Fr(cert['T'])
    terms = {}          # exact rational distance -> coefficient (Fraction)
    dterms = []         # (arb distance, Fraction coefficient) for non-exact distances
    Lsum = Fr(0)
    for j, cf in enumerate(cert['configs']):
        P, tris, E = replay(sides, cf['ops'])
        n = len(P)
        # all points distinct (well separated)
        for p, q in itertools.combinations(range(n), 2):
            assert abs(P[p] - P[q]) > 0, "coincident points"
        y = {}
        for k, v in cf['y'].items():
            p, q = map(int, k.split(',')); assert 0 <= p < q < n; y[(p, q)] = Fr(v)
        pats = patterns(n, tris)
        assert pats, "no admissible pattern (then L = +inf; not used)"
        Lj = min(sum(v * s[p] * s[q] for (p, q), v in y.items()) for s in pats)
        Lsum += Lj
        for (p, q), v in y.items():
            if (p, q) in E: terms[E[(p, q)]] = terms.get(E[(p, q)], Fr(0)) + v
            else: dterms.append((abs(P[q] - P[p]), v))
        if verbose: print(f"  config {j}: n={n}, constructed triangles {len(tris)}, patterns {len(pats)}, L={float(Lj):.6f}")
    musum = Fr(0)
    for X in cert['aux']:
        r = [Fr(v) for v in X['r']]; sg = X['sg']; mu = Fr(X['mu'])
        assert mu >= 0 and all(v > 0 for v in r) and all(z in (1, -1) for z in sg)
        assert r[0] <= r[1] + r[2] and r[1] <= r[0] + r[2] and r[2] <= r[0] + r[1], "aux triangle inequality"
        assert min(sg[0] * s[0] * s[1] + sg[1] * s[0] * s[2] + sg[2] * s[1] * s[2]
                   for s in itertools.product((1, -1), repeat=3)) >= -1
        for v, z in zip(r, sg): terms[v] = terms.get(v, Fr(0)) + mu * z
        musum += mu
    Lam = Lsum - musum
    assert Lam > 0, f"Lam = {float(Lam)} <= 0"
    lam = A(Lam)
    # term list: (arb r, arb coef)
    TL = [(A(r), A(w)) for r, w in terms.items() if w != 0] + [(d, A(w)) for d, w in dterms if w != 0]
    # merge identical arb distances is not needed; tail bound
    Ta = A(T)
    tail = sum((abs(w) * (2 / (arb.pi() * r * Ta)).sqrt() for r, w in TL), arb(0))
    assert tail.upper() < lam.lower(), f"tail bound {tail} not below Lam = {float(Lam)} at T = {float(T)}"
    M2 = sum((abs(w) * r * r for r, w in TL), arb(0))
    # adaptive cells, initial width 1/8
    K = -((-T * 8) // 1)                      # ceil(8T): cells cover [0, K/8] >= [0, T]
    assert Fr(K, 8) >= T
    stack = [(Fr(k, 8), Fr(k + 1, 8)) for k in range(int(K) - 1, -1, -1)]
    cells = 0; worst = -10.0
    while stack:
        lo, hi = stack.pop(); cc = (lo + hi) / 2; rad = (hi - lo) / 2
        x = A(cc); ra = A(rad)
        h = arb(0); hp = arb(0)
        for r, w in TL:
            z = r * x; h += w * z.bessel_j(0); hp += w * r * z.bessel_j(1)
        ub = h + abs(hp) * ra + M2 * ra * ra / 2
        if ub.upper() < lam.lower():
            cells += 1; worst = max(worst, float(h.mid())); continue
        assert rad > Fr(1, 10**7), f"f >= Lam near t = {float(cc)}: f ~ {h}, Lam = {float(Lam)}"
        stack += [(cc, hi), (lo, cc)]
    if verbose:
        print(f"  Lam = {float(Lam):.6f}, max f at cell centres ~ {worst:.6f}, tail(T={float(T)}) <= {float(tail.upper()):.4f}, "
              f"{len(TL)} terms, {cells} cells, {time.time() - t0:.0f}s")
    return Lam

# ======================================================================= interval certificates
INT_DOC = """'173-pattern-int-v1': rho in [lo, hi] (rationals, 1/2 < lo <= hi < 1).  Claim: for every algebraic rho in
[lo, hi] and every algebraic b in [rho, 1], every 2-colouring of the plane has a monochromatic copy of (rho, b, 1).
Proof: for such T, Lemma A makes every triangle with sides in {rho, b, 1} a.s. non-monochromatic; the four
triangles with sides in {rho, 1} ((rho,rho,rho), (1,1,1), (rho,1,1), (rho,rho,1); valid since rho > 1/2) are among
them, and the certificate only uses these (base triangle (rho,1,1)), C(rho) and C(1).  All geometry is evaluated
with rho as an arb ball containing [lo, hi]; every enclosure is valid for each rho in the interval."""

def replay_int(lo, hi, ops):
    rb = (A(lo) + A(hi)) / 2 + arb(0, float(hi - lo) / 2 * (1 + 1e-9) + 1e-30)
    val = {'rho': rb, '1': arb(1)}
    def valid(x, y, z):
        for r in (lo, hi):
            v = {'rho': r, '1': Fr(1)}; X, Y, Z = v[x], v[y], v[z]
            if not (X + Y > Z and X + Z > Y and Y + Z > X): return False
        return True
    def place(x, y, z):
        assert valid(x, y, z), "invalid family triangle on the interval"
        X, Y, Z = val[x], val[y], val[z]
        px = (Y ** 2 + Z ** 2 - X ** 2) / (2 * Z); h2 = Y ** 2 - px ** 2
        assert h2 > 0; return [acb(0), acb(Z), acb(px, h2.sqrt())]
    assert ops[0] == ['T']
    P = place('rho', '1', '1'); tris = [(0, 1, 2)]; E = {(0, 1): '1', (0, 2): '1', (1, 2): 'rho'}
    for op in ops[1:]:
        assert op[0] == 'gv', "interval certificates: only vertex gluings"
        _, sd, j, refl, v, m = op
        x, y, z = sd; assert all(w in ('rho', '1') for w in sd)
        S = place(x, y, z)
        if refl: S = [q.conjugate() for q in S]
        m = Fr(m); rotc = acb(A((1 - m * m) / (1 + m * m)), A(2 * m / (1 + m * m)))
        idx = []
        for k in range(3):
            if k == j: idx.append(v)
            else: P.append(P[v] + (S[k] - S[j]) * rotc); idx.append(len(P) - 1)
        for (p, q), l in {(0, 1): z, (0, 2): y, (1, 2): x}.items():
            E[(min(idx[p], idx[q]), max(idx[p], idx[q]))] = l
        tris.append(tuple(sorted(idx)))
    return P, tris, E, rb

# ---- mean-value-form geometry for interval certificates: dual numbers (value at rho_mid, derivative over ball)
class D:
    """f(rho) represented by (v, dv): v = enclosure of f(rho_mid), dv = enclosure of f'(rho) over the rho ball."""
    def __init__(self, v, dv): self.v = v; self.dv = dv
    def __add__(s, o): return D(s.v + o.v, s.dv + o.dv)
    def __sub__(s, o): return D(s.v - o.v, s.dv - o.dv)
    def __mul__(s, o): return D(s.v * o.v, s.dv * o.vb + s.vb * o.dv)
def Dc(vm, vb, dv):
    d = D(vm, dv); d.vb = vb; return d     # vb = enclosure of f over the whole ball (for product rule)

def replay_int_mv(lo, hi, ops):
    """returns for each point: (value at mid [acb], value over ball [acb], derivative over ball [acb])."""
    rm = A((lo + hi) / 2); rb = (A(lo) + A(hi)) / 2 + arb(0, float(hi - lo) / 2 * (1 + 1e-9) + 1e-30)
    def side(w, r): return r if w == 'rho' else arb(1)
    def dside(w): return arb(1) if w == 'rho' else arb(0)
    def tri(x, y, z, r):
        X, Y, Z = side(x, r), side(y, r), side(z, r); dX, dY, dZ = dside(x), dside(y), dside(z)
        px = (Y * Y + Z * Z - X * X) / (2 * Z)
        dpx = ((2 * Y * dY + 2 * Z * dZ - 2 * X * dX) * Z - (Y * Y + Z * Z - X * X) * dZ) / (2 * Z * Z)
        h2 = Y * Y - px * px; assert h2 > 0; h = h2.sqrt(); dh = (Y * dY - px * dpx) / h
        return [(acb(0), acb(0)), (acb(Z), acb(dZ)), (acb(px, h), acb(dpx, dh))]
    def place(x, y, z):
        m = tri(x, y, z, rm); b = tri(x, y, z, rb)
        return [(m[k][0], b[k][0], b[k][1]) for k in range(3)]
    P = place('rho', '1', '1')
    for op in ops[1:]:
        _, sd, j, refl, v, mm = op
        S = place(*sd)
        if refl: S = [(a.conjugate(), b.conjugate(), c.conjugate()) for a, b, c in S]
        mm = Fr(mm); rotc = acb(A((1 - mm * mm) / (1 + mm * mm)), A(2 * mm / (1 + mm * mm)))
        for k in range(3):
            if k == j: continue
            P.append(tuple(P[v][i] + (S[k][i] - S[j][i]) * rotc for i in range(3)))
    return P, rm, rb

def dist_mv(P, p, q, lo, hi):
    """enclosure of |P_q(rho) - P_p(rho)| over rho in [lo, hi] by the mean value form."""
    dm = P[q][0] - P[p][0]; db = P[q][1] - P[p][1]; ddb = P[q][2] - P[p][2]
    absb = abs(db); assert absb > 0
    deriv = abs((db.conjugate() * ddb).real / absb)        # |d/drho |Delta|| over the ball
    return abs(dm) + arb(0, float(deriv.upper()) * float(hi - lo) / 2 * (1 + 1e-9))

J1MAX = A(Fr(5819, 10**4))   # max |J1| = 0.58186... < 0.5819
def j0_enc(z):
    """J0 over a real ball z: mean value form (|J0'| = |J1| <= 0.5819), intersected with |J0(x)| <= sqrt(2/(pi x))."""
    zm = arb(z.mid()); e = zm.bessel_j(0) + arb(0, float((J1MAX * arb(z.rad())).upper()))
    zl = arb(z.lower())
    if zl > 0:
        B = (2 / (arb.pi() * zl)).sqrt(); lo_ = max(float(e.lower()), -float(B.upper())); hi_ = min(float(e.upper()), float(B.upper()))
        if hi_ - lo_ < float(e.upper()) - float(e.lower()):
            # rounding of the float endpoints outward
            lo_ = lo_ - 1e-15 * (1 + abs(lo_)); hi_ = hi_ + 1e-15 * (1 + abs(hi_))
            return arb((lo_ + hi_) / 2, (hi_ - lo_) / 2 * (1 + 1e-12))
    return e
def j1_enc(z):
    """J1 over a real ball z (|J1'| <= 1)."""
    zm = arb(z.mid()); return zm.bessel_j(1) + arb(0, float(arb(z.rad()).upper()))

def check_int(cert, verbose=True):
    t0 = time.time()
    assert cert['type'] == '173-pattern-int-v1'
    lo, hi = [Fr(x) for x in cert['rho']]; assert Fr(1, 2) < lo <= hi < 1
    T = Fr(cert['T']); terms = {}; famterms = {'rho': Fr(0), '1': Fr(0)}; dterms = []; Lsum = Fr(0)
    for j, cf in enumerate(cert['configs']):
        P, tris, E, rb = replay_int(lo, hi, cf['ops']); n = len(P)
        Pmv, _, _ = replay_int_mv(lo, hi, cf['ops'])
        for p, q in itertools.combinations(range(n), 2): assert abs(P[p] - P[q]) > 0, "coincident points"
        y = {}
        for k, v in cf['y'].items():
            p, q = map(int, k.split(',')); assert 0 <= p < q < n; y[(p, q)] = Fr(v)
        pats = patterns(n, tris); assert pats
        Lj = min(sum(v * s[p] * s[q] for (p, q), v in y.items()) for s in pats); Lsum += Lj
        for (p, q), v in y.items():
            if (p, q) in E: famterms[E[(p, q)]] += v
            else: dterms.append((dist_mv(Pmv, p, q, lo, hi), v))
        if verbose: print(f"  config {j}: n={n}, triangles {len(tris)}, patterns {len(pats)}, L={float(Lj):.6f}")
    musum = Fr(0)
    for X in cert['aux']:
        r = [Fr(v) for v in X['r']]; sg = X['sg']; mu = Fr(X['mu'])
        assert mu >= 0 and all(v > 0 for v in r) and all(z in (1, -1) for z in sg)
        assert r[0] <= r[1] + r[2] and r[1] <= r[0] + r[2] and r[2] <= r[0] + r[1]
        assert min(sg[0] * s[0] * s[1] + sg[1] * s[0] * s[2] + sg[2] * s[1] * s[2]
                   for s in itertools.product((1, -1), repeat=3)) >= -1
        for v, z in zip(r, sg): terms[v] = terms.get(v, Fr(0)) + mu * z
        musum += mu
    Lam = Lsum - musum; assert Lam > 0; lam = A(Lam)
    TL = [(A(r), A(w)) for r, w in terms.items() if w != 0]
    TL += [(rb if k == 'rho' else arb(1), A(w)) for k, w in famterms.items() if w != 0]
    TL += [(d, A(w)) for d, w in dterms if w != 0]
    Ta = A(T)
    tail = sum((abs(w) * (2 / (arb.pi() * arb(r.lower()) * Ta)).sqrt() for r, w in TL), arb(0))
    assert tail.upper() < lam.lower(), f"tail {tail} >= Lam"
    M2 = sum((abs(w) * arb(r.upper()) ** 2 for r, w in TL), arb(0))
    K = -((-T * 8) // 1); stack = [(Fr(k, 8), Fr(k + 1, 8)) for k in range(int(K) - 1, -1, -1)]
    cells = 0; worst = -10.0
    while stack:
        lo_, hi_ = stack.pop(); cc = (lo_ + hi_) / 2; rad = (hi_ - lo_) / 2; x = A(cc); ra = A(rad)
        h = arb(0); hp = arb(0)
        for r, w in TL:
            z = r * x; h += w * j0_enc(z); hp += w * r * j1_enc(z)
        ub = h + abs(hp) * ra + M2 * ra * ra / 2
        if ub.upper() < lam.lower(): cells += 1; worst = max(worst, float(h.upper())); continue
        assert rad > Fr(1, 10**6), f"f >= Lam near t = {float(cc)}: f in {h}, Lam = {float(Lam)}"
        stack += [(cc, hi_), (lo_, cc)]
    if verbose:
        print(f"  rho in [{float(lo)}, {float(hi)}]: Lam = {float(Lam):.6f}, max upper(f) at centres {worst:.6f}, "
              f"{len(TL)} terms, {cells} cells, {time.time() - t0:.0f}s")
    return Lam

# ======================================================================= v2: first-order Taylor in rho
INT2_DOC = """'173-pattern-int-v2': same claim and soundness as int-v1; f(t; rho) for rho in [lo, hi] is bounded by
  f(t; rho_m) + (dr/2) |d/drho f(t; rho_m)| + (dr^2/8) sup_{rho} |d^2/drho^2 f(t; rho)|,   dr = hi - lo,
(Taylor with Lagrange remainder in rho), with d/drho J0(r(rho) t) = -t r' J1(r t),
  |d^2/drho^2 J0(r(rho) t)| = |-t r'' J1 - t^2 r'^2 J1'| <= 0.5819 t |r''| + t^2 r'^2   (|J1| <= 0.5819, |J1'| <= 1).
r, r', r'' of every distance come from second-order forward AD of the exact construction: at the exact midpoint
(r, r') and over the rho ball (sup |r'|, sup |r''|).  t-cells: second-order Taylor in t for f_m and for
g = d/drho f_m (|g''| <= sum |W r'| (2 r + t r^2)), the remainder term evaluated at the cell's upper end."""

class H:
    """second-order forward AD over acb: (v, d, dd) = (f, f', f'') w.r.t. rho."""
    def __init__(self, v, d=None, dd=None):
        self.v = acb(v); self.d = acb(0) if d is None else acb(d); self.dd = acb(0) if dd is None else acb(dd)
    def __add__(s, o): o = o if isinstance(o, H) else H(o); return H(s.v + o.v, s.d + o.d, s.dd + o.dd)
    __radd__ = __add__
    def __sub__(s, o): o = o if isinstance(o, H) else H(o); return H(s.v - o.v, s.d - o.d, s.dd - o.dd)
    def __rsub__(s, o): return H(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, H) else H(o)
        return H(s.v * o.v, s.d * o.v + s.v * o.d, s.dd * o.v + 2 * s.d * o.d + s.v * o.dd)
    __rmul__ = __mul__
    def inv(s):
        iv = 1 / s.v; return H(iv, -s.d * iv * iv, (2 * s.d * s.d * iv - s.dd) * iv * iv)
    def __truediv__(s, o): o = o if isinstance(o, H) else H(o); return s * o.inv()
    def sqrt(s):
        r = s.v.sqrt(); return H(r, s.d / (2 * r), (2 * s.dd * s.v - s.d * s.d) / (4 * s.v * r))
    def conj(s): return H(s.v.conjugate(), s.d.conjugate(), s.dd.conjugate())

def replay_H(ops, rho):
    """points as H (functions of rho) evaluated at the arb ball/point rho (real)."""
    R = H(acb(rho), acb(1), acb(0)); one = H(acb(1))
    def side(w): return R if w == 'rho' else one
    def place(x, y, z):
        X, Y, Z = side(x), side(y), side(z)
        px = (Y * Y + Z * Z - X * X) / (Z * 2); h = (Y * Y - px * px).sqrt()
        return [H(0), Z, px + h * acb(0, 1)]
    P = place('rho', '1', '1')
    for op in ops[1:]:
        _, sd, j, refl, v, mm = op
        S = place(*sd)
        if refl: S = [q.conj() for q in S]
        mm = Fr(mm); rotc = acb(A((1 - mm * mm) / (1 + mm * mm)), A(2 * mm / (1 + mm * mm)))
        for k in range(3):
            if k == j: continue
            P.append(P[v] + (S[k] - S[j]) * rotc)
    return P

def dist_H(P, p, q):
    """r, r', r'' (real arb) of |P_q - P_p|."""
    D = P[q] - P[p]; n2 = D * D.conj()                 # |D|^2 as H (real-valued)
    r = n2.sqrt()
    return r.v.real, r.d.real, r.dd.real

def check_int2(cert, verbose=True):
    t0 = time.time()
    assert cert['type'] == '173-pattern-int-v2'
    lo, hi = [Fr(x) for x in cert['rho']]; assert Fr(1, 2) < lo <= hi < 1
    rm = (lo + hi) / 2; dr = hi - lo; drA = A(dr)
    rball = (A(lo) + A(hi)) / 2 + arb(0, float(dr) / 2 * (1 + 1e-9) + 1e-30)
    T = Fr(cert['T']); Lsum = Fr(0)
    TL = []        # (r_m, r'_m, sup|r'|, sup|r''|, inf r, w)  as arbs
    exact = {}
    for j, cf in enumerate(cert['configs']):
        P0, tris, E, _ = replay_int(lo, hi, cf['ops']); n = len(P0)         # validity checks + exact edges
        for p, q in itertools.combinations(range(n), 2): assert abs(P0[p] - P0[q]) > 0
        Pm = replay_H(cf['ops'], A(rm)); Pb = replay_H(cf['ops'], rball)
        y = {}
        for k, v in cf['y'].items():
            p, q = map(int, k.split(',')); assert 0 <= p < q < n; y[(p, q)] = Fr(v)
        pats = patterns(n, tris); assert pats
        Lj = min(sum(v * s[p] * s[q] for (p, q), v in y.items()) for s in pats); Lsum += Lj
        for (p, q), v in y.items():
            if (p, q) in E: exact[E[(p, q)]] = exact.get(E[(p, q)], Fr(0)) + v; continue
            r_m, d_m, _ = dist_H(Pm, p, q); r_b, d_b, dd_b = dist_H(Pb, p, q)
            assert r_b > 0
            TL.append((r_m, d_m, arb(abs(d_b).upper()), arb(abs(dd_b).upper()), arb(r_b.lower()), A(v), True))
        if verbose: print(f"  config {j}: n={n}, triangles {len(tris)}, patterns {len(pats)}, L={float(Lj):.6f}")
    musum = Fr(0); auxt = {}
    for X in cert['aux']:
        r = [Fr(v) for v in X['r']]; sg = X['sg']; mu = Fr(X['mu'])
        assert mu >= 0 and all(v > 0 for v in r) and all(z in (1, -1) for z in sg)
        assert r[0] <= r[1] + r[2] and r[1] <= r[0] + r[2] and r[2] <= r[0] + r[1]
        assert min(sg[0] * s[0] * s[1] + sg[1] * s[0] * s[2] + sg[2] * s[1] * s[2]
                   for s in itertools.product((1, -1), repeat=3)) >= -1
        for v, z in zip(r, sg): auxt[v] = auxt.get(v, Fr(0)) + mu * z
        musum += mu
    Lam = Lsum - musum; assert Lam > 0; lam = A(Lam)
    for r, w in auxt.items():
        if w: TL.append((A(r), arb(0), arb(0), arb(0), A(r), A(w), False))
    if exact.get('1'): TL.append((arb(1), arb(0), arb(0), arb(0), arb(1), A(exact['1']), False))
    if exact.get('rho'): TL.append((A(rm), arb(1), arb(1), arb(0), A(lo), A(exact['rho']), True))
    Ta = A(T)
    tail = sum((abs(w) * (2 / (arb.pi() * rl * Ta)).sqrt() for (_, _, _, _, rl, w, _) in TL), arb(0))
    assert tail.upper() < lam.lower(), f"tail {tail} >= Lam"
    rmax = [arb(r.upper()) + arb(dsup.upper()) * drA / 2 for (r, _, dsup, _, _, _, _) in TL]
    M2f = sum((abs(w) * rx * rx for (_, _, _, _, _, w, _), rx in zip(TL, rmax)), arb(0))
    K = -((-T * 8) // 1); stack = [(Fr(k, 8), Fr(k + 1, 8)) for k in range(int(K) - 1, -1, -1)]
    cells = 0; worst = -10.0
    while stack:
        a_, b_ = stack.pop(); cc = (a_ + b_) / 2; rad = (b_ - a_) / 2; x = A(cc); ra = A(rad); xh = A(b_)
        f = arb(0); fp = arb(0); g = arb(0); gp = arb(0); Mg = arb(0); rem = arb(0)
        for (r, d, dsup, ddsup, rl, w, var), rx in zip(TL, rmax):
            z = r * x; j0 = z.bessel_j(0); j1 = z.bessel_j(1)
            f += w * j0; fp += w * r * j1                       # |f'| = |sum w r J1|
            if var:
                g += w * d * x * j1                             # g = -sum w r' t J1 (sign irrelevant: |g|)
                j1p = j0 - j1 / z
                gp += w * d * (j1 + x * r * j1p)
                Mg += abs(w) * abs(d) * (2 * rx + xh * rx * rx)
                rem += abs(w) * (A(Fr(5819, 10**4)) * xh * ddsup + xh * xh * dsup * dsup)
        ub = f + abs(fp) * ra + M2f * ra * ra / 2
        ub += drA / 2 * (abs(g) + abs(gp) * ra + Mg * ra * ra / 2) + drA * drA / 8 * rem
        if ub.upper() < lam.lower(): cells += 1; worst = max(worst, float(f.upper())); continue
        assert rad > Fr(1, 10**6), f"f >= Lam near t = {float(cc)}: ub {ub}, Lam = {float(Lam)}"
        stack += [(cc, b_), (a_, cc)]
    if verbose:
        print(f"  rho in [{float(lo)}, {float(hi)}]: Lam = {float(Lam):.6f}, max f(rho_m) at centres {worst:.6f}, "
              f"{len(TL)} terms, {cells} cells, {time.time() - t0:.0f}s")
    return Lam

if __name__ == "__main__":
    for fn in sys.argv[1:]:
        cert = json.load(open(fn))
        if cert['type'] == '173-pattern-int-v2':
            check_int2(cert)
            print(f"{fn}: VERIFIED for every rho in {cert['rho']} and every b in [rho, 1]: triangle (rho, b, 1) is forced"); continue
        if cert['type'] == '173-pattern-int-v1':
            check_int(cert)
            print(f"{fn}: VERIFIED for every rho in {cert['rho']} and every b in [rho, 1]: triangle (rho, b, 1) is forced"); continue
        print(f"{fn}: sides {cert['sides']}")
        check(cert)
        print(f"{fn}: VERIFIED (every 2-colouring of the plane contains a monochromatic copy of T = {tuple(cert['sides'])})")
