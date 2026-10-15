"""Independent referee checker for the Erdos #173 'beyond' 1-D certification (research/triangles173_beyond).

Written from the mathematical definition. It shares no code with research/triangles173_beyond/*.py or with the
other verify_mine checkers; only the JSON *format* of the certificates is read (it has to be).

CLAIM checked: for every algebraic rho in [RHO_LO, RHO_HI] and every algebraic b in [rho, 1], every red/blue
colouring of R^2 contains a monochromatic congruent copy of the triangle (rho, b, 1).  (By scaling: every
triangle with algebraic side ratios whose shortest/longest ratio lies in [RHO_LO, RHO_HI].)

SOUNDNESS (family reduction, research/triangles173_beyond/NOTES.md s.1; paper/ramsey.tex Thm tri).
  If a colouring has no monochromatic copy of T = (rho, b, 1), Folner averaging over E x| K gives an invariant
  random +-1 colouring sigma of the algebraic plane E with C(r) = E s(x)s(y) = a0 + int_(0,inf) J0(r t) dnu(t)
  for r > 0, a0 >= 0, a0 + |nu| <= 1 (OpenAI Thm 2.3), a.s. without monochromatic copies of T in E.
  Lemma A: C(rho)+C(b)+C(1) = -1 (T a.s. non-mono, pair sum -1) and 3C(s) >= -1 (equilateral) => all = -1/3.
  Then every triangle with sides in {rho, 1} (valid since 2 rho > 1) has pair-sum Z >= -1 with E Z = -1, so it
  is a.s. non-monochromatic, simultaneously for all of its countably many copies in E.
  A certificate for rho in I is a finite list of point configurations in E built from (rho,1,1) by gluing
  triangles with sides in {rho,1} via exact rigid motions, with pair weights y, plus aux triangles (rational
  sides, signs sg with sum sg s s >= -1 for all patterns) with weights mu >= 0.  With L_j = exact min of
  sum y_pq s_p s_q over sign patterns with no constructed triangle monochromatic,
      Lam := sum_j L_j - sum mu  <=  E[...]  =  int f(t; rho) dG(t)  <=  max(0, sup_t f(t; rho)),
      f(t; rho) = sum_j sum_pq y_pq J0(d_pq(rho) t) + sum_aux mu sum_i sg_i J0(r_i t).
  So Lam > 0 and sup_{t >= 0, rho in I} f < Lam is a contradiction.  A strip box [[a0,a1],[1,1]]
  (verify_box format) is the special case of the single triangle (a,1,1) with a in [a0,a1].

WHAT THIS PROGRAM DOES
  * geometry: points are 2nd-order arb power series in rho (python-flint arb_series), evaluated (i) at the exact
    rational centre of a rho-cell -> d, d' there, and (ii) on an arb ball containing the rho-cell -> rigorous
    enclosures of d, d', d'' for every rho in the cell.  Template triangle (x,y,z): V0=0, V1=Z, V2=(px,h),
    px=(Y^2+Z^2-X^2)/2Z, h=sqrt(Y^2-px^2) (h^2 > 0 checked on the ball); rotation ((1-m^2),2m)/(1+m^2) (exact
    unit, checked in Q); reflection = conjugation.  So every constructed triangle is congruent to its template,
    i.e. an exact family triangle for every rho (structural); additionally each constructed edge is
    compared numerically with its label at the cell centre (implementation sanity check).
  * forbidden triangles = the constructed ones only (forbidding fewer is conservative: L_j can only drop).
  * patterns: all 2^(n-1) sign vectors with s_0 = +1; L_j exact Fraction.  Aux rows: r_i > 0, (degenerate)
    triangle inequality, validity on all 8 patterns, mu >= 0.  Weighted pairs: d^2 > 0 on the whole rho-cell.
  * sup f < Lam on [0,T] x I by adaptive 2-D cells [tc +- tau] x [rc +- delta] with the 2nd-order Taylor bound
        f <= f(c) + |f_t(c)| tau + |f_rho(c)| delta + (Mtt tau^2 + 2 Mtr tau delta + Mrr delta^2)/2,
    Mtt = sum|w| D^2, Mtr = sum|w| |d'| (0.5819 + D t1), Mrr = sum|w| (0.5819 t1 |d''| + t1^2 d'^2)
    (|J1| <= 0.5819, |J1'| = |J0 - J2|/2 <= 1, sups of D,|d'|,|d''| over the rho-cell from the ball).
    J0 from fastlib/j0fast (|err| <= 1e-14); J1(x) = -(J0(x+h)-J0(x-h))/2h, h = 2^-13, error
    <= h^2/6 (|J1''| <= 1) + rounding; every float error is bounded explicitly (global slack, asserted
    < 1e-6, added).  Failing cells are split in t or in rho (whichever part of the bound dominates);
    the certificate data are the same for every rho in I, so splitting rho is legitimate.
  * tail t >= T: |J0(x)| <= sqrt(2/(pi x)) (x(J0^2+Y0^2) increases to 2/pi), sum |w| sqrt(2/(pi dmin T)) < Lam.
  * coverage: the union of the verified rho-intervals (exact rationals) contains [RHO_LO, RHO_HI].
usage: check_beyond173.py [--lo 0.86125 --hi 0.88465] [--only] cert files...   (exit 0 iff all pass + covered)
"""
import sys, os, json, hashlib, itertools, time, math, argparse
from fractions import Fraction as Fr
import numpy as np
from flint import arb, arb_series, ctx
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))   # j0fast.py + libj0fast.dylib in certificates/triangles/
from j0fast import j0 as J0F, ERR as J0ERR

ctx.prec = 128
ctx.cap = 3
NS = 3                      # series length: value, first, second order
U = 2.0 ** -53              # unit roundoff
J1MAX = 0.5819              # max |J1| = 0.58186522...
H = 2.0 ** -13              # finite-difference step for J1
SLACK_MAX = 1e-6


class Fail(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Fail(msg)


def A(q):
    q = Fr(q); return arb(q.numerator) / arb(q.denominator)


def fup(x):
    """float upper bound of an arb."""
    v = float(arb(x).upper()); return v + abs(v) * 4.5e-16 + 1e-300


def flo(x):
    v = float(arb(x).lower()); return v - abs(v) * 4.5e-16 - 1e-300


def fmid(x):
    """(float m, err) with |x_true - m| <= err for every point of the ball x."""
    m = float(x.mid()); return m, float(arb(x.rad()).upper()) * (1 + 1e-12) + abs(m) * 2.3e-16 + 1e-300


def sconst(v):
    return arb_series([v], prec=NS)


# ------------------------------------------------------------------------------------------------ parsing
def parse_cert(c, fname, idx):
    """normalise a certificate to: rho interval [lo,hi] (Fractions), list of configs (ops with labels, y),
    aux rows, T.  Strip boxes become a single 3-point config."""
    if 'box' in c:
        (a0, a1), (b0, b1) = [[Fr(x) for x in iv] for iv in c['box']]
        need(b0 == 1 and b1 == 1, "strip box must have b-interval [1,1]")
        y = [Fr(v) for v in c['y']]
        need(len(y) == 3, "box y must have 3 entries")
        # points 0,1,2 of (a,1,1): |01| = 1, |02| = 1, |12| = a.  y = (y_a, y_b, y_1); b = 1.
        cfg = {'ops': [['T']], 'y': {(1, 2): y[0], (0, 2): y[1], (0, 1): y[2]}}
        return dict(kind='strip', lo=a0, hi=a1, configs=[cfg], aux=c['aux'], T=Fr(c['T']), name=f"{fname}[{idx}]")
    typ = c.get('type')
    if typ in ('173-pattern-int-v1', '173-pattern-int-v2'):
        lo, hi = [Fr(x) for x in c['rho']]; lab = None
    elif typ == '173-pattern-v1':
        s = [Fr(x) for x in c['sides']]
        need(s[1] == 1 and s[2] == 1, "single-shape certs: only sides (rho,1,1) supported")
        lo = hi = s[0]; lab = {s[0]: 'rho', Fr(1): '1'}
    else:
        raise Fail(f"unknown certificate type {typ}")
    cfgs = []
    for cf in c['configs']:
        ops = []
        for op in cf['ops']:
            if op[0] == 'T':
                need(len(op) == 1, "bad T op"); ops.append(['T'])
            elif op[0] == 'gv':
                need(len(op) == 6, "bad gv op")
                _, sd, j, refl, v, m = op
                if lab is not None:
                    need(all(Fr(x) in lab for x in sd), "glued triangle side not in {rho,1}")
                    sd = [lab[Fr(x)] for x in sd]
                need(len(sd) == 3 and all(x in ('rho', '1') for x in sd), "glued triangle labels must be rho/1")
                need(isinstance(j, int) and 0 <= j <= 2, "bad glue vertex j")
                need(isinstance(refl, bool), "bad reflection flag")
                need(isinstance(v, int) and v >= 0, "bad glue point v")
                ops.append(['gv', list(sd), j, refl, v, Fr(m)])
            else:
                raise Fail(f"unsupported op {op[0]}")
        y = {}
        for k, w in cf['y'].items():
            p, q = (int(x) for x in k.split(','))
            need(0 <= p < q, f"bad pair key {k}")
            need((p, q) not in y, f"duplicate pair {k}")
            y[(p, q)] = Fr(w)
        cfgs.append({'ops': ops, 'y': y})
    return dict(kind=typ, lo=lo, hi=hi, configs=cfgs, aux=c['aux'], T=Fr(c['T']), name=f"{fname}[{idx}]")


# ------------------------------------------------------------------------------------------------ combinatorics
def combinatorics(cfg):
    """from ops: number of points, constructed triangles, edge labels. (Geometry-free; the geometry built in
    geometry() follows exactly the same rules, so each constructed triangle is congruent to its template.)"""
    ops = cfg['ops']
    need(ops and ops[0] == ['T'], "config must start with T")
    n = 3; tris = [(0, 1, 2)]
    E = {(0, 1): '1', (0, 2): '1', (1, 2): 'rho'}           # T = (rho,1,1): V0V1 = z=1, V0V2 = y=1, V1V2 = x=rho
    for op in ops[1:]:
        _, (x, yv, z), j, refl, v, m = op
        need(v < n, "glue point index out of range")
        idx = []
        for k in range(3):
            if k == j: idx.append(v)
            else: idx.append(n); n += 1
        tris.append(tuple(idx))
        for (a, b), l in (((0, 1), z), ((0, 2), yv), ((1, 2), x)):
            key = (min(idx[a], idx[b]), max(idx[a], idx[b]))
            need(E.get(key, l) == l, "edge with two different labels")
            E[key] = l
    return n, tris, E


def min_energy(n, tris, y):
    best = None; cnt = 0
    for bits in itertools.product((1, -1), repeat=n - 1):
        s = (1,) + bits
        if any(s[a] == s[b] == s[c] for (a, b, c) in tris): continue
        e = sum(w * s[p] * s[q] for (p, q), w in y.items())
        cnt += 1
        if best is None or e < best: best = e
    need(cnt > 0, "no admissible pattern")
    return best, cnt


def aux_check(aux):
    const = {}; musum = Fr(0)
    for X in aux:
        r = [Fr(v) for v in X['r']]; sg = X['sg']; mu = Fr(X['mu'])
        need(len(r) == 3 and len(sg) == 3, "aux shape")
        need(mu >= 0, "aux mu < 0")
        need(all(v > 0 for v in r), "aux r <= 0")
        need(2 * max(r) <= sum(r), "aux triangle inequality")
        need(all(z in (1, -1) for z in sg), "aux signs")
        need(min(sg[0] * s[0] * s[1] + sg[1] * s[0] * s[2] + sg[2] * s[1] * s[2]
                 for s in itertools.product((1, -1), repeat=3)) >= -1, "aux row invalid for some pattern")
        for v, z in zip(r, sg): const[v] = const.get(v, Fr(0)) + mu * z
        musum += mu
    return const, musum


# ------------------------------------------------------------------------------------------------ geometry
def geometry(ops, rho):
    """points as pairs of arb_series in (rho - rho0), rho0 = the arb `rho` (point or ball)."""
    R = arb_series([rho, arb(1)], prec=NS); ONE = sconst(arb(1)); ZERO = sconst(arb(0))
    side = {'rho': R, '1': ONE}

    def template(x, yv, z):
        X, Y, Z = side[x], side[yv], side[z]
        px = (Y * Y + Z * Z - X * X) / (Z * 2)
        h2 = Y * Y - px * px
        need(len(h2.coeffs()) > 0 and h2.coeffs()[0] > 0, "template height^2 not provably > 0")
        return [(ZERO, ZERO), (Z, ZERO), (px, h2.sqrt())]

    P = template('rho', '1', '1')
    for op in ops[1:]:
        _, (x, yv, z), j, refl, v, m = op
        S = template(x, yv, z)
        if refl: S = [(a, -b) for (a, b) in S]
        cq, sq = (1 - m * m) / (1 + m * m), 2 * m / (1 + m * m)
        need(cq * cq + sq * sq == 1, "rotation not a unit")
        c, s = A(cq), A(sq)
        for k in range(3):
            if k == j: continue
            dx, dy = S[k][0] - S[j][0], S[k][1] - S[j][1]
            P.append((P[v][0] + dx * c - dy * s, P[v][1] + dx * s + dy * c))
    return P


def dist_series(P, p, q):
    dx = P[q][0] - P[p][0]; dy = P[q][1] - P[p][1]
    n2 = dx * dx + dy * dy
    need(len(n2.coeffs()) > 0 and n2.coeffs()[0] > 0, f"distance ({p},{q}) not provably > 0 on the rho-cell")
    c = list(n2.sqrt().coeffs())
    return c + [arb(0)] * (NS - len(c))


class Problem:
    """one certificate: exact Lam, constant terms, rho-exact term, variable (geometric) terms."""

    def __init__(self, cert, log):
        self.name = cert['name']; self.lo, self.hi = cert['lo'], cert['hi']; self.T = cert['T']
        need(Fr(1, 2) < self.lo <= self.hi < 1, "rho interval must lie in (1/2, 1)")
        need(self.T > 0, "T > 0")
        Lsum = Fr(0); self.var = []                 # (config index, p, q, weight)
        self.const, musum = aux_check(cert['aux'])
        self.wrho = Fr(0); self.cfgs = []
        for ci, cfg in enumerate(cert['configs']):
            n, tris, E = combinatorics(cfg)
            for (p, q) in cfg['y']: need(q < n, "pair index out of range")
            L, npat = min_energy(n, tris, cfg['y'])
            Lsum += L
            for (p, q), w in cfg['y'].items():
                if w == 0: continue
                if (p, q) in E:
                    if E[(p, q)] == 'rho': self.wrho += w
                    else: self.const[Fr(1)] = self.const.get(Fr(1), Fr(0)) + w
                else: self.var.append((ci, p, q, w))
            self.cfgs.append((cfg['ops'], E, n))
            log(f"    config {ci}: n={n}, constructed triangles {len(tris)}, admissible patterns {npat}, L={float(L):.6f}")
        self.Lam = Lsum - musum
        self.Lsum, self.musum = Lsum, musum
        need(self.Lam > 0, f"Lam = {float(self.Lam)} <= 0")
        if self.lo == self.hi and self.lo in self.const:      # single shape: aux side equal to rho is the rho term
            self.wrho += self.const.pop(self.lo)
        self.const = {r: w for r, w in self.const.items() if w != 0}
        self.cache = {}
        self.structural_check()

    def structural_check(self):
        """templates valid (h^2 > 0) on the whole rho-interval; every constructed edge has its label length at
        the centre (implementation sanity check of the op interpretation; exactness itself is structural)."""
        lo, hi = self.lo, self.hi; rc = (lo + hi) / 2
        ball = (A(lo) + A(hi)) / 2 + arb(0, float(hi - lo) / 2 * (1 + 1e-9) + 1e-40)
        for ops, E, n in self.cfgs:
            geometry(ops, ball); Pc = geometry(ops, A(rc))
            need(len(Pc) == n, "geometry/combinatorics point count mismatch")
            for (p, q), l in E.items():
                dc = dist_series(Pc, p, q)[0]
                tv = A(rc) if l == 'rho' else arb(1)
                need(abs(float((dc - tv).mid())) < 1e-25 and float(arb(dc.rad()).upper()) < 1e-20,
                     f"constructed edge ({p},{q}) does not have length {l}")

    def celldata(self, a, b):
        """float arrays for rho-cell [a,b]: w, d(centre), err_d, d'(centre), err_d1, Dsup, d1sup, d2sup, dmin."""
        key = (a, b)
        if key in self.cache: return self.cache[key]
        rc = (a + b) / 2
        ball = (A(a) + A(b)) / 2 + arb(0, float(b - a) / 2 * (1 + 1e-9) + 1e-40)
        need(ball.lower() <= A(a) and ball.upper() >= A(b), "ball does not contain the cell")
        rows = []
        # constant terms (exact rational r)
        for r, w in self.const.items():
            rf = float(r)
            rows.append((float(w), rf, abs(rf) * 1.2e-16, 0.0, 0.0, rf * (1 + 1e-15), 0.0, 0.0, rf * (1 - 1e-15)))
        # rho-exact term d(rho) = rho
        if self.wrho != 0:
            m, e = fmid(A(rc))
            rows.append((float(self.wrho), m, e, 1.0, 0.0, fup(A(b)), 1.0, 0.0, flo(A(a))))
        # geometric terms
        byc = {}
        for (ci, p, q, w) in self.var: byc.setdefault(ci, []).append((p, q, w))
        for ci, lst in byc.items():
            ops, E, n = self.cfgs[ci]
            Pc = geometry(ops, A(rc)); Pb = geometry(ops, ball)
            for (p, q, w) in lst:
                c0 = dist_series(Pc, p, q); cb = dist_series(Pb, p, q)
                d, ed = fmid(c0[0]); d1, ed1 = fmid(c0[1])
                rows.append((float(w), d, ed, d1, ed1, fup(cb[0]), fup(abs(cb[1])), fup(abs(cb[2] * 2)), flo(cb[0])))
        arr = np.array(rows, dtype=np.float64)
        need(np.all(arr[:, 8] > 0), "some weighted distance has no positive lower bound")
        self.cache[key] = arr
        return arr


# ------------------------------------------------------------------------------------------------ the sweep
def errJ1(xmax):
    return H * H / 6 + (2 * J0ERR + J1MAX * U * 2 * (xmax + H)) / (2 * H) + 4 * U


def sweep(P, log, N0=16384, chunk=2_000_000, record=None):
    T = float(P.T); lo, hi = P.lo, P.hi
    lam = flo(A(P.Lam))
    root = P.celldata(lo, hi)
    w = root[:, 0]; aw = np.abs(w)
    # Fraction -> float weight error: |w_f - w| <= u|w|; affects f by <= u|w| (|J0| <= 1), handled in slack
    # tail
    tail = arb(0)
    for (r, ww) in P.const.items(): tail += abs(A(ww)) * (2 / (arb.pi() * A(r) * A(P.T))).sqrt()
    for row in root[len(P.const):]:
        tail += abs(arb(row[0])) * (1 + 1e-15) * (2 / (arb.pi() * arb(row[8]) * A(P.T))).sqrt()
    need(tail.upper() < A(P.Lam).lower(), f"tail bound {float(tail.upper()):.6f} >= Lam {float(P.Lam):.6f} at T={T}")
    nT = len(w)

    def slack_for(cd, tau_max, delta):
        # explicit bound on all floating-point errors of f(c), f_t(c), f_rho(c) for this rho-cell
        aw_ = np.abs(cd[:, 0]); D = cd[:, 5]; ed = cd[:, 2]; ed1 = cd[:, 4]; d1 = np.abs(cd[:, 3]) + ed1
        eJ1 = errJ1(float(D.max()) * T * (1 + 1e-12) + 1)
        xerr = (2 * U * D + ed) * T                       # |fl(d t) - d_true t|
        eF = np.sum(aw_ * (J0ERR + J1MAX * xerr + 2 * U)) + (nT + 3) * U * np.sum(aw_)
        eFt = np.sum(aw_ * ((D + ed) * (eJ1 + xerr) + ed * J1MAX)) + (nT + 3) * U * np.sum(aw_ * D) * 2
        eFr = np.sum(aw_ * (d1 * T * (eJ1 + xerr) + ed1 * T * J1MAX)) + (nT + 3) * U * np.sum(aw_ * d1) * T * 2
        s = 2 * (eF + eFt * tau_max + eFr * delta) + 1e-12
        need(s < SLACK_MAX, f"float slack {s} too large")
        return s

    edges = np.linspace(0.0, T, N0 + 1)
    tau0 = T / N0 / 2
    queue = [(lo, hi, (edges[:-1] + edges[1:]) / 2, np.full(N0, tau0))]
    ncell = 0; nrho = 1; worst = -1e300; worst_ub = -1e300; maxslack = 0.0; rho_cells = set()
    while queue:
        a, b, tc_all, tau_all = queue.pop()
        cd = P.celldata(a, b)
        delta = float(b - a) / 2 * (1 + 1e-12)
        W = cd[:, 0]; d = cd[:, 1]; d1 = cd[:, 3]; D = cd[:, 5]; S1 = cd[:, 6]; S2 = cd[:, 7]; AW = np.abs(W)
        Mtt = float(np.sum(AW * D * D)) * (1 + 1e-12)
        A1 = float(np.sum(AW * S1)) * J1MAX * (1 + 1e-12); A2 = float(np.sum(AW * S1 * D)) * (1 + 1e-12)
        B1 = float(np.sum(AW * S2)) * J1MAX * (1 + 1e-12); B2 = float(np.sum(AW * S1 * S1)) * (1 + 1e-12)
        sl = slack_for(cd, float(tau_all.max()) if len(tau_all) else 0.0, delta)
        maxslack = max(maxslack, sl)
        rho_split_tc, rho_split_tau = [], []
        tc, tau = tc_all, tau_all
        while tc.size:
            step = max(1, chunk // len(W))
            new_tc, new_tau = [], []
            for s0 in range(0, tc.size, step):
                t = tc[s0:s0 + step]; ta = tau[s0:s0 + step]
                X = d[:, None] * t[None, :]
                j0 = J0F(X)
                j1 = -(J0F(X + H) - J0F(X - H)) / (2 * H)
                F = W @ j0
                Ft = -(W * d) @ j1
                Fr_ = -((W * d1) @ j1) * t
                ta = ta * (1 + 1e-9) + 1e-12          # covers float rounding of cell centres/edges
                t1 = t + ta
                Mtr = A1 + A2 * t1; Mrr = B1 * t1 + B2 * t1 * t1
                tpart = np.abs(Ft) * ta + 0.5 * Mtt * ta * ta
                rpart = np.abs(Fr_) * delta + Mtr * ta * delta + 0.5 * Mrr * delta * delta
                ub = F + tpart + rpart + sl
                ok = ub < lam
                ncell += int(ok.sum())
                if record is not None and ok.any():
                    record.append((a, b, t[ok], ta[ok], ub[ok]))
                if ok.any():
                    worst = max(worst, float(F[ok].max())); worst_ub = max(worst_ub, float(ub[ok].max()))
                bad = ~ok
                if bad.any():
                    need(np.all(F[bad] + sl < lam), f"f >= Lam at t = {float(t[bad][np.argmax(F[bad])]):.6f}, "
                         f"rho-cell [{float(a):.9f},{float(b):.9f}]: f = {float(F[bad].max()):.6f}, Lam = {lam:.6f}")
                    tsplit = bad & (tpart >= rpart)
                    rsplit = bad & ~(tpart >= rpart)
                    if tsplit.any():
                        tt, tw = t[tsplit], ta[tsplit] / 2
                        need(tw.min() > 1e-9, f"t-cell too small near t = {float(tt[0])}")
                        new_tc += [tt - tw, tt + tw]; new_tau += [tw, tw]
                    if rsplit.any():
                        rho_split_tc.append(t[rsplit]); rho_split_tau.append(ta[rsplit])
            tc = np.concatenate(new_tc) if new_tc else np.empty(0)
            tau = np.concatenate(new_tau) if new_tau else np.empty(0)
        if rho_split_tc:
            need(b - a > Fr(1, 10**13), f"rho-cell too small at {float(a)}")
            m = (a + b) / 2; tcs = np.concatenate(rho_split_tc); taus = np.concatenate(rho_split_tau)
            queue.append((a, m, tcs, taus)); queue.append((m, b, tcs.copy(), taus.copy())); nrho += 2
    return dict(Lam=float(P.Lam), tail=float(tail.upper()), cells=ncell, rho_cells=nrho, maxf=worst,
                maxub=worst_ub, slack=maxslack)



# ------------------------------------------------------------------------------------------------ negative controls
def run_one(c, name='x'):
    """returns None on PASS, else the failure message."""
    try:
        check_one(parse_cert(c, name, 0), lambda s: None); return None
    except Fail as e:
        return str(e)
    except (KeyError, ValueError, TypeError, ZeroDivisionError, IndexError) as e:
        return f"malformed ({type(e).__name__}: {e})"


def tamper(certdir):
    import copy
    ld = lambda f: json.load(open(os.path.join(certdir, f)))
    A_, B_ = ld('int2_band_A.json'), ld('int2_band_B.json')
    S1, S2 = ld('strip_086125_0869.json'), ld('strip_0869_0879.json')
    def mod(c, fn):
        c = copy.deepcopy(c); fn(c); return c
    def setcfg(k, i, v):
        def f(c): c['configs'][k]['ops'][i] = v
        return f
    def scale_y(k, key, fac):
        def f(c): c['configs'][k]['y'][key] = str(Fr(c['configs'][k]['y'][key]) * Fr(fac))
        return f
    def first_var_key(c):
        pc = parse_cert(c, 'x', 0)
        for k, cf in enumerate(pc['configs']):
            E = combinatorics(cf)[2]
            for key in c['configs'][k]['y']:
                if tuple(map(int, key.split(','))) not in E: return k, key
    def biggest_var_key(c):
        pc = parse_cert(c, 'x', 0); best = (0, None, None)
        for k, cf in enumerate(pc['configs']):
            E = combinatorics(cf)[2]
            for key, w in c['configs'][k]['y'].items():
                if tuple(map(int, key.split(','))) not in E and abs(Fr(w)) > best[0]: best = (abs(Fr(w)), k, key)
        return best[1], best[2]
    b21 = B_[21]; a0 = A_[0]; kc, k_b = first_var_key(b21); kg, k_g = biggest_var_key(b21)
    op = b21['configs'][kc]['ops'][1]; lg = len(b21['configs'][kg]['ops']) - 1; opg = b21['configs'][kg]['ops'][lg]
    tests = [
        ("control: int2_band_B[21] untouched", b21, True),
        ("control: strip_0869_0879[5] untouched", S2[5], True),
        ("B[21]: rho interval moved to [0.8870, 0.8871]", mod(b21, lambda c: c.__setitem__('rho', ['8870/10000', '8871/10000'])), False),
        ("B[21]: rho interval widened to [0.88464375, 0.8860]", mod(b21, lambda c: c.__setitem__('rho', [c['rho'][0], '443/500'])), False),
        ("A[0]: rho interval widened to [0.870426, 0.8740]", mod(a0, lambda c: c.__setitem__('rho', [c['rho'][0], '437/500'])), False),
        ("B[21]: rotation m of config %d op 1 changed by +1/100 (small weights there; still valid: dense float max 0.9973 < 1)" % kc,
         mod(b21, setcfg(kc, 1, op[:5] + [str(Fr(op[5]) + Fr(1, 100))])), True),
        ("B[21]: rotation m of config %d op %d changed by +1/10 (op carrying the largest off-family weight)" % (kg, lg),
         mod(b21, setcfg(kg, lg, opg[:5] + [str(Fr(opg[5]) + Fr(1, 10))])), False),
        ("B[21]: reflection flag of config %d op 1 flipped" % kc, mod(b21, setcfg(kc, 1, op[:3] + [not op[3]] + op[4:])), False),
        ("B[21]: glued template of config %d op 1 relabelled (rho,rho,rho)" % kc,
         mod(b21, setcfg(kc, 1, [op[0], ['rho', 'rho', 'rho']] + op[2:])), False),
        ("B[21]: off-family weight %s in config %d scaled x1.01 (still valid: dense float max 0.9972 < Lam 0.99938)" % (k_b, kc), mod(b21, scale_y(kc, k_b, Fr(101, 100))), True),
        ("B[21]: largest off-family weight %s in config %d scaled x2" % (k_g, kg), mod(b21, scale_y(kg, k_g, 2)), False),
        ("B[21]: tightness: extra aux row (50,50,50), sg (1,1,1), mu = 0.0035 lowers Lam to 0.9965 < float max f ~0.9970",
         mod(b21, lambda c: c['aux'].append({'r': ['50', '50', '50'], 'sg': [1, 1, 1], 'mu': '7/2000'})), False),
        ("B[21]: tightness: same with mu = 0.0025 (Lam 0.9975 > max f; expected to pass)",
         mod(b21, lambda c: c['aux'].append({'r': ['50', '50', '50'], 'sg': [1, 1, 1], 'mu': '1/400'})), True),
        ("B[21]: all aux rows removed", mod(b21, lambda c: c.__setitem__('aux', [])), False),
        ("B[21]: aux row 0 signs -> (1,1,-1) (invalid)", mod(b21, lambda c: c['aux'][0].__setitem__('sg', [1, 1, -1])), False),
        ("B[21]: aux row 0 mu negated", mod(b21, lambda c: c['aux'][0].__setitem__('mu', str(-Fr(c['aux'][0]['mu'])))), False),
        ("B[21]: T lowered to 300 (tail)", mod(b21, lambda c: c.__setitem__('T', 300.0)), False),
        ("A[0]: pair weight moved to another pair", mod(a0, lambda c: c['configs'][1]['y'].__setitem__('1,6', c['configs'][1]['y'].pop('1,5'))), False),
        ("strip_0869_0879[5]: a-interval moved to [0.875, 0.876]", mod(S2[5], lambda c: c['box'].__setitem__(0, ['7/8', '219/250'])), False),
        ("strip_0869_0879[5]: b-interval [0.99, 1] (not a strip)", mod(S2[5], lambda c: c['box'].__setitem__(1, ['99/100', '1'])), False),
        ("strip_086125_0869[0]: all y scaled x1.01 (still valid: dense float max 1.0335 < Lam 1.0578)", mod(S1[0], lambda c: c.__setitem__('y', [str(Fr(v) * Fr(101, 100)) for v in c['y']])), True),
        ("strip_086125_0869[0]: y_a alone scaled x1.05", mod(S1[0], lambda c: c['y'].__setitem__(0, str(Fr(c['y'][0]) * Fr(105, 100)))), False),
    ]
    bad = 0
    for desc, c, expect_pass in tests:
        r = run_one(c)
        good = (r is None) == expect_pass
        bad += not good
        print(f"  {'ok ' if good else 'BAD'}  {desc}: " + ("PASS" if r is None else "FAIL - " + r[:110]), flush=True)
    # coverage gap: drop one interval of band B
    ivs = sorted([(Fr(c['box'][0][0]), Fr(c['box'][0][1])) for c in S1 + S2] + [(Fr(c['rho'][0]), Fr(c['rho'][1])) for c in A_ + B_[:10] + B_[11:]])
    reach = Fr('0.86125')
    for a, b in ivs:
        if a > reach: break
        reach = max(reach, b)
    good = reach < Fr('0.88465'); bad += not good
    print(f"  {'ok ' if good else 'BAD'}  coverage with int2_band_B[10] dropped: reach {float(reach):.6f} -> " + ("GAP detected" if good else "no gap?!"))
    print("NEGATIVE CONTROLS: " + ("all behaved as expected" if bad == 0 else f"{bad} UNEXPECTED"))
    return bad == 0

# ------------------------------------------------------------------------------------------------ driver
def check_one(cert, log):
    t0 = time.time()
    P = Problem(cert, log)
    res = sweep(P, log)
    res['time'] = time.time() - t0
    return P, res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lo', default='0.86125'); ap.add_argument('--hi', default='0.88465')
    ap.add_argument('--nocover', action='store_true', help='skip the coverage check')
    ap.add_argument('--quiet', action='store_true')
    ap.add_argument('--tamper', metavar='CERTDIR', help='run the negative controls on the certificates in CERTDIR')
    ap.add_argument('files', nargs='*')
    args = ap.parse_args()
    if args.tamper: sys.exit(0 if tamper(args.tamper) else 1)
    log = (lambda s: None) if args.quiet else (lambda s: print(s, flush=True))
    ivs = []; nfail = 0; t0 = time.time()
    for fn in args.files:
        raw = open(fn, 'rb').read()
        print(f"== {fn}  sha256 {hashlib.sha256(raw).hexdigest()[:16]}", flush=True)
        L = json.loads(raw)
        if isinstance(L, dict): L = [L]
        for i, c in enumerate(L):
            try:
                cert = parse_cert(c, os.path.basename(fn), i)
                P, r = check_one(cert, log)
                print(f"  PASS {cert['name']}: rho in [{cert['lo']}, {cert['hi']}] = [{float(cert['lo']):.9f}, "
                      f"{float(cert['hi']):.9f}]  Lam={r['Lam']:.6f}  max f(centres)={r['maxf']:.6f}  "
                      f"max ub={r['maxub']:.6f}  tail={r['tail']:.4f}  cells={r['cells']}  rho-cells={r['rho_cells']}  "
                      f"slack={r['slack']:.1e}  {r['time']:.1f}s", flush=True)
                ivs.append((cert['lo'], cert['hi'], cert['name']))
            except Fail as e:
                nfail += 1
                print(f"  FAIL {os.path.basename(fn)}[{i}]: {e}", flush=True)
    ok = nfail == 0
    if not args.nocover:
        lo, hi = Fr(args.lo), Fr(args.hi)
        ivs.sort(); reach = lo; gap = None
        for a, b, _ in ivs:
            if b < reach: continue
            if a > reach: gap = reach; break
            reach = max(reach, b)
            if reach >= hi: break
        covered = reach >= hi
        print(f"COVERAGE of [{lo}, {hi}] by {len(ivs)} verified intervals: "
              + ("COMPLETE" if covered else f"GAP at {float(gap if gap is not None else reach):.9f} (reach {float(reach):.9f})"))
        ok = ok and covered
    print(("ALL PASS" if ok else f"NOT VERIFIED ({nfail} certificate failures)") + f"  [{time.time() - t0:.0f}s]")
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
