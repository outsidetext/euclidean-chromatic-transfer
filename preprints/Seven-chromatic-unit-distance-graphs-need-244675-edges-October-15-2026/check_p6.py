#!/usr/bin/env python3
"""Independent rigorous checker for the monochromatic unit-pair density p of a periodic colouring
of the plane given by exact-rational convex polygons (format of research/chi6_devil/maps/*_exact.json:
{"B": [[x,y],[x,y]], "polys": [[[x,y],...],...], "cols": [...]}, coordinates ints or "a/b" strings).

Written from scratch; imports nothing from the repo.

Definition.  p = P[c(x) = c(x + u)], x uniform on R^2/Lambda, u uniform on S^1.  Summing over ordered
same-colour piece pairs (i, j, lambda):
    p = 1/(2 pi covol) * sum I(P_i, P_j + lambda),   I(P,Q) = int_P int_Q delta(|y - x| - 1) dy dx.

Method (different from the theta-integration of area(P cap (Q - u)) used by certify.py/indep_check.py):
DOUBLE GREEN / boundary-pair formula.  If Delta psi = delta(r - 1) in the plane with psi radial, then
    int_P int_Q (Delta psi)(y - x) dy dx = - sum_{e in dP} sum_{e' in dQ} (n_e . n_e') int_e int_e' psi(|x - y|) ds ds'.
Two choices of psi:
  psi+ = log+ r = max(log r, 0):  Delta psi+ = delta(r-1)              ->  I = - sum (n.n') iint log+|x-y|
  psi- = log- r = min(log r, 0):  Delta psi- = 2 pi delta_0 - delta(r-1) ->  I = 2 pi |P cap Q| + sum (n.n') iint log-|x-y|
(psi- is used only when dist(P, Q) > 1/2, where |P cap Q| = 0 and the kernel is smooth on dP x dQ.)
For each edge pair the inner integral over e' is done in closed form,
    int log sqrt(tau^2 + h^2) dtau = tau/2 log(tau^2+h^2) - tau + h atan(tau/h),
restricted to |y - x| >= 1 (psi+) or <= 1 (psi-); the outer integral over e is done with arb's rigorous
adaptive Gauss-Legendre integrator (acb.integral, holomorphy verified on every subinterval), after
splitting [0,1] at every point where the case structure changes (h = 0, +-1; tau0 = 0, tau1 = 0;
|x - endpoint| = 1).  Breakpoints are enclosed in exact dyadic intervals whose contribution is bounded by
width * L' * max|psi|.

Validity checks on the input (exact rational arithmetic, python-flint fmpq): every coordinate is an int or
"a/b" string; at most 6 colours (override --max-colours for tests); every polygon strictly convex; lattice
translates of the pieces have pairwise disjoint interiors (exact separating-axis test over a provably
complete set of lattice vectors); sum of areas == covolume (so the translates tile up to a null set).

usage: check_p6.py map.json [--workers 4] [--prec 128] [--max-colours 6] [--split auto|plus|both]
       check_p6.py --selftest
"""
import sys, os, json, math, time, argparse
from fractions import Fraction
from flint import fmpq, fmpz, arb, acb, ctx

# ------------------------------------------------------------------ exact geometry
def parseQ(s):
    if isinstance(s, bool):
        raise Rejected('bad coordinate %r' % (s,))
    if isinstance(s, int):
        return fmpq(s)
    if isinstance(s, str):
        s = s.strip()
        if '/' in s:
            a, b = s.split('/')
            a, b = int(a), int(b)
            if b == 0:
                raise Rejected('zero denominator')
            return fmpq(a, b)
        return fmpq(int(s))
    raise Rejected('coordinate must be an int or "a/b" string, got %r (floats rejected)' % (s,))


def vsub(a, b): return (a[0] - b[0], a[1] - b[1])
def vadd(a, b): return (a[0] + b[0], a[1] + b[1])
def vdot(a, b): return a[0] * b[0] + a[1] * b[1]
def vcross(a, b): return a[0] * b[1] - a[1] * b[0]


def signed_area2(P):
    n = len(P)
    return sum(vcross(P[k], P[(k + 1) % n]) for k in range(n))


def strictly_convex_ccw(P):
    n = len(P)
    if n < 3:
        return False
    for k in range(n):
        if vcross(vsub(P[(k + 1) % n], P[k]), vsub(P[(k + 2) % n], P[(k + 1) % n])) <= 0:
            return False
    # winding number 1 (no star polygons): total turning = 2 pi  <=> sum of exterior angles; for strictly
    # left-turning closed polygon this holds iff the polygon is simple; check via the angle-sorting test:
    # all vertices must lie on the left of every edge line.
    for k in range(n):
        a, b = P[k], P[(k + 1) % n]
        for m in range(n):
            if m != k and m != (k + 1) % n and vcross(vsub(b, a), vsub(P[m], a)) <= 0:
                return False
    return True


def interiors_disjoint(P, Q):
    """convex polygons (CCW): interiors disjoint iff some edge line of P or Q weakly separates them"""
    for A, Bp in ((P, Q), (Q, P)):
        n = len(A)
        for k in range(n):
            a, b = A[k], A[(k + 1) % n]
            d = vsub(b, a)
            # outward side of edge (a,b) for CCW polygon = right side: cross(d, v - a) <= 0
            if all(vcross(d, vsub(v, a)) <= 0 for v in Bp):
                return True
    return False


def pt_seg_d2(p, a, b):
    d = vsub(b, a)
    t = vdot(vsub(p, a), d) / vdot(d, d)
    if t < 0:
        t = fmpq(0)
    elif t > 1:
        t = fmpq(1)
    w = vsub(p, (a[0] + t * d[0], a[1] + t * d[1]))
    return vdot(w, w)


def segs_intersect(a, b, c, d):
    def orient(p, q, r):
        v = vcross(vsub(q, p), vsub(r, p))
        return (v > 0) - (v < 0)
    o1, o2, o3, o4 = orient(a, b, c), orient(a, b, d), orient(c, d, a), orient(c, d, b)
    if o1 != o2 and o3 != o4:
        return True
    def onseg(p, q, r):
        return min(p[0], q[0]) <= r[0] <= max(p[0], q[0]) and min(p[1], q[1]) <= r[1] <= max(p[1], q[1])
    if o1 == 0 and onseg(a, b, c): return True
    if o2 == 0 and onseg(a, b, d): return True
    if o3 == 0 and onseg(c, d, a): return True
    if o4 == 0 and onseg(c, d, b): return True
    return False


def seg_seg_mind2(a, b, c, d):
    if segs_intersect(a, b, c, d):
        return fmpq(0)
    return min(pt_seg_d2(a, c, d), pt_seg_d2(b, c, d), pt_seg_d2(c, a, b), pt_seg_d2(d, a, b))


def poly_mind2(P, Q):
    """exact squared distance between two convex polygons with disjoint interiors"""
    best = None
    for k in range(len(P)):
        for m in range(len(Q)):
            x = seg_seg_mind2(P[k], P[(k + 1) % len(P)], Q[m], Q[(m + 1) % len(Q)])
            if best is None or x < best:
                best = x
    return best


def poly_maxd2(P, Q):
    return max(vdot(vsub(v, w), vsub(v, w)) for v in P for w in Q)


# ------------------------------------------------------------------ loading / validation
class Rejected(Exception):
    pass


def load_map(D, max_colours=6):
    if not isinstance(D, dict) or set(D.keys()) - {'B', 'polys', 'cols'} or not {'B', 'polys', 'cols'} <= set(D.keys()):
        raise Rejected('JSON must have exactly keys B, polys, cols')
    B = [tuple(parseQ(x) for x in row) for row in D['B']]
    if len(B) != 2 or any(len(r) != 2 for r in B):
        raise Rejected('B must be 2x2')
    covol = vcross(B[0], B[1])
    if covol == 0:
        raise Rejected('degenerate lattice')
    covol = abs(covol)
    polys = []
    for i, P in enumerate(D['polys']):
        Q = [tuple(parseQ(x) for x in v) for v in P]
        if any(len(v) != 2 for v in P):
            raise Rejected('vertex not 2D in polygon %d' % i)
        a2 = signed_area2(Q)
        if a2 == 0:
            raise Rejected('polygon %d has zero area' % i)
        if a2 < 0:
            Q = Q[::-1]
        if not strictly_convex_ccw(Q):
            raise Rejected('polygon %d is not strictly convex' % i)
        polys.append(Q)
    cols = D['cols']
    if len(cols) != len(polys):
        raise Rejected('cols length mismatch')
    if any(not isinstance(c, int) or isinstance(c, bool) for c in cols):
        raise Rejected('colours must be ints')
    if len(set(cols)) > max_colours:
        raise Rejected('%d colours used, more than %d' % (len(set(cols)), max_colours))
    area = sum(signed_area2(P) for P in polys) / 2
    if area != covol:
        raise Rejected('sum of piece areas %s != covolume %s' % (area, covol))
    return B, polys, cols, covol


def lattice_box(B, R):
    """all integer (a,b) such that |a B0 + b B1| <= R is possible: |a| <= R|B1|/det, |b| <= R|B0|/det"""
    det = abs(float(vcross(B[0], B[1])))
    n0 = math.hypot(float(B[0][0]), float(B[0][1]))
    n1 = math.hypot(float(B[1][0]), float(B[1][1]))
    A = int(math.floor(R * n1 / det * (1 + 1e-9))) + 1
    Bb = int(math.floor(R * n0 / det * (1 + 1e-9))) + 1
    return [(a, b) for a in range(-A, A + 1) for b in range(-Bb, Bb + 1)]


def lat(B, ab):
    return (ab[0] * B[0][0] + ab[1] * B[1][0], ab[0] * B[0][1] + ab[1] * B[1][1])


def candidate_pairs(B, polys, extra):
    """all (i, j, ab) with |c_i - c_j - lam| <= r_i + r_j + extra, where c = first vertex and r = an
    exact upper bound on max |v - c|  (complete: any x in P_i, y in P_j + lam within distance `extra`)."""
    c = [P[0] for P in polys]
    # exact squared radii, then float upper bounds with margin
    r = [math.sqrt(float(max(vdot(vsub(v, P[0]), vsub(v, P[0])) for v in P))) * (1 + 1e-12) + 1e-12 for P in polys]
    rmax = max(r)
    cmax = max(math.hypot(float(v[0]), float(v[1])) for v in c)
    box = lattice_box(B, 2 * cmax + 2 * rmax + extra + 1e-6)
    out = []
    import numpy as np
    C = np.array([[float(v[0]), float(v[1])] for v in c])
    Rr = np.array(r)
    L = np.array([[float(x) for x in lat(B, ab)] for ab in box])
    for i in range(len(polys)):
        Dx = C[i, 0] - C[None, :, 0] - L[:, None, 0]
        Dy = C[i, 1] - C[None, :, 1] - L[:, None, 1]
        dist = np.hypot(Dx, Dy)
        ok = dist <= (Rr[i] + Rr[None, :] + extra) * (1 + 1e-9) + 1e-9
        li, jj = np.nonzero(ok)
        for l, j in zip(li, jj):
            out.append((i, int(j), box[int(l)]))
    return out


def check_tiling(B, polys):
    n = 0
    for (i, j, ab) in candidate_pairs(B, polys, 0.0):
        if ab == (0, 0) and j == i:
            continue
        if (j, i, (-ab[0], -ab[1])) < (i, j, ab):
            continue
        lam = lat(B, ab)
        Q = [vadd(v, lam) for v in polys[j]]
        if not interiors_disjoint(polys[i], Q):
            raise Rejected('pieces %d and %d+%s overlap' % (i, j, ab))
        n += 1
    return n


# ------------------------------------------------------------------ rigorous edge-pair integral
PREC = 128
DY = 220   # dyadic rounding exponent for breakpoint enclosures


def q2arb(q):
    return arb(q)


def dyadic_floor(x):
    """largest k/2^DY <= x for x an fmpq or an arb lower bound"""
    if isinstance(x, arb):
        x = arb_lo_q(x)
    return fmpq((x.p * (fmpz(2) ** DY)) // x.q, fmpz(2) ** DY)


def dyadic_ceil(x):
    if isinstance(x, arb):
        x = arb_hi_q(x)
    return fmpq(-((-x.p * (fmpz(2) ** DY)) // x.q), fmpz(2) ** DY)


def arb_exact_q(a):
    m, e = a.man_exp()
    m, e = int(m), int(e)
    return fmpq(m) * fmpq(2) ** e if e >= 0 else fmpq(m, 2 ** (-e))


def arb_lo_q(a):
    return arb_exact_q(a.lower())


def arb_hi_q(a):
    return arb_exact_q(a.upper())


def acb_atan(w, an):
    # atan(w) = (log(1 + i w) - log(1 - i w)) / (2 i), principal branches; cut = atan's cut
    I = acb(0, 1)
    return ((1 + I * w).log(analytic=an) - (1 - I * w).log(analytic=an)) / (2 * I)


def edge_pair_integral(A, D, Bv, Dp, mode, psibound, stats):
    """rigorous enclosure of  int_0^1 G(s) ds,  G(s) = int_{y in e'} psi(|A + s D - y|) dl(y),
    e' = [Bv, Bv + Dp], psi = log+ (mode '+') or log- (mode '-')."""
    k = vdot(D, Dp)
    Lq2 = vdot(Dp, Dp)
    Lp = arb(Lq2).sqrt()
    W0 = vsub(Bv, A)
    W1 = vadd(W0, Dp)
    a0 = vdot(W0, Dp)
    c0 = vcross(Dp, W0)
    k2 = vcross(Dp, D)
    Dd = vdot(D, D)
    zero, one = fmpq(0), fmpq(1)
    # ---- breakpoints as exact intervals
    bps = []
    def add_exact(q):
        if zero < q < one:
            bps.append((dyadic_floor(q), dyadic_ceil(q)))
    def add_arb(t):
        lo, hi = arb_lo_q(t), arb_hi_q(t)
        if hi > zero and lo < one:
            bps.append((dyadic_floor(lo), dyadic_ceil(hi)))
    if k2 != 0:
        add_exact(c0 / k2)
        add_arb((arb(c0) - Lp) / arb(k2))
        add_arb((arb(c0) + Lp) / arb(k2))
    if k != 0:
        add_exact(a0 / k)
        add_exact((a0 + Lq2) / k)
    for W in (W0, W1):
        # |W - s D|^2 = 1 :  Dd s^2 - 2 (W.D) s + |W|^2 - 1 = 0
        bq = vdot(W, D)
        disc = bq * bq - Dd * (vdot(W, W) - 1)
        if disc == 0:
            add_exact(bq / Dd)
        elif disc > 0:
            sq = arb(disc).sqrt()
            add_arb((arb(bq) - sq) / arb(Dd))
            add_arb((arb(bq) + sq) / arb(Dd))
    bps.append((zero, zero))
    bps.append((one, one))
    bps.sort(key=lambda z: (float(z[0]), z[0]))
    # merge
    cl = []
    for lo, hi in sorted(bps, key=lambda z: z[0]):
        if cl and lo <= cl[-1][1]:
            if hi > cl[-1][1]:
                cl[-1][1] = hi
        else:
            cl.append([lo, hi])
    total = arb(0)
    # cluster contributions (clipped to [0,1])
    Lpb = arb(Lq2).sqrt()
    for lo, hi in cl:
        lo2 = max(lo, zero)
        hi2 = min(hi, one)
        if hi2 > lo2:
            total += arb(0, arb(hi2 - lo2) * Lpb * psibound)
            stats['clusterw'] = stats.get('clusterw', 0) + float(hi2 - lo2)
    # gaps
    for kk in range(len(cl) - 1):
        g0 = max(cl[kk][1], zero)
        g1 = min(cl[kk + 1][0], one)
        if not g1 > g0:
            continue
        sm = (g0 + g1) / 2
        T0L = a0 - k * sm           # tau0 * Lp
        T1L = T0L + Lq2             # tau1 * Lp
        HL = c0 - k2 * sm           # h * Lp
        h2 = HL * HL / Lq2
        Wm0 = vsub(W0, (sm * D[0], sm * D[1]))
        Wm1 = vsub(W1, (sm * D[0], sm * D[1]))
        d0 = vdot(Wm0, Wm0)
        d1 = vdot(Wm1, Wm1)
        if h2 != 1:
            assert d0 != 1 and d1 != 1, 'breakpoint inside gap'
        big = h2 >= 1
        # classify tau0, tau1 relative to [-c, c]
        def cls(TL, d):
            if big:
                return 'out'      # unused
            if d < 1:
                return 'in'
            return 'neg' if TL < 0 else 'pos'
        s0, s1 = cls(T0L, d0), cls(T1L, d1)
        pieces = []   # (alpha_sym, beta_sym, kind) ; syms: 't0','t1','-c','c' ; kind 'plain'|'comb'
        sgn = lambda TL: 1 if TL > 0 else (-1 if TL < 0 else 0)
        if mode == '+':
            if big:
                pieces.append(('t0', 't1', 'plain'))
            else:
                if s0 == 'neg':
                    pieces.append(('t0', 't1' if s1 == 'neg' else '-c', 'comb'))
                if s1 == 'pos':
                    pieces.append(('t0' if s0 == 'pos' else 'c', 't1', 'comb'))
        else:
            if not big and not (s1 == 'neg' or s0 == 'pos'):
                al = 't0' if s0 == 'in' else '-c'
                be = 't1' if s1 == 'in' else 'c'
                sa = sgn(T0L) if al == 't0' else -1
                sb = sgn(T1L) if be == 't1' else 1
                assert sa != 0 and sb != 0
                pieces.append((al, be, 'comb' if sa * sb > 0 else 'plain'))
        if not pieces:
            continue
        needc = any('c' in p[0] or 'c' in p[1] for p in pieces)
        a0b, kb, c0b, k2b, Lq2b = arb(a0), arb(k), arb(c0), arb(k2), arb(Lq2)

        def f(s, an):
            Lpa = acb(Lpb)
            T0 = (a0b - kb * s) / Lpa
            T1 = T0 + Lpa
            H = (c0b - k2b * s) / Lpa
            H2 = H * H
            vals = {'t0': T0, 't1': T1}
            if needc:
                C = (1 - H2).sqrt(analytic=an)
                vals['c'] = C
                vals['-c'] = -C
            tot = acb(0)
            for (al, be, kind) in pieces:
                x, y = vals[al], vals[be]
                tot += y * (y * y + H2).log(analytic=an) / 2 - y - x * (x * x + H2).log(analytic=an) / 2 + x
                if kind == 'plain':
                    tot += H * (acb_atan(y / H, an) - acb_atan(x / H, an))
                else:
                    tot += H * acb_atan(H * (y - x) / (H2 + x * y), an)
            return tot

        J = acb.integral(f, acb(arb(g0)), acb(arb(g1)), rel_tol=arb(2) ** (-100), abs_tol=arb(2) ** (-110))
        stats['nint'] = stats.get('nint', 0) + 1
        if not J.imag.contains(0) or J.imag.rad() > arb(2) ** (-60):
            raise ArithmeticError('integral has nonzero imaginary part %s' % J.imag)
        total += J.real
    return total


def pair_integral(P, Q, mode, stats):
    """enclosure of I(P,Q) = iint delta(|x-y|-1) via the boundary-pair formula with psi = log+ or log-"""
    nP, nQ = len(P), len(Q)
    tot = arb(0)
    for kk in range(nP):
        A, A2 = P[kk], P[(kk + 1) % nP]
        D = vsub(A2, A)
        for mm in range(nQ):
            Bv, B2 = Q[mm], Q[(mm + 1) % nQ]
            Dp = vsub(B2, Bv)
            k = vdot(D, Dp)
            if k == 0:
                continue                      # n.n' = 0
            if mode == '+':
                M2 = max(vdot(vsub(u, w), vsub(u, w)) for u in (A, A2) for w in (Bv, B2))
                if M2 <= 1:
                    continue                  # log+ == 0 on e x e'
                psib = arb(M2).log() / 2
            else:
                m2 = seg_seg_mind2(A, A2, Bv, B2)
                if m2 >= 1:
                    continue                  # log- == 0 on e x e'
                psib = -arb(m2).log() / 2
            J = edge_pair_integral(A, D, Bv, Dp, mode, psib, stats)
            coef = arb(k) / arb(vdot(Dp, Dp)).sqrt()     # (D.D')/L'
            tot += coef * J
            stats['nedge'] = stats.get('nedge', 0) + 1
    return -tot if mode == '+' else tot


# ------------------------------------------------------------------ driver
def build_tasks(B, polys, cols):
    tasks = []
    for (i, j, ab) in candidate_pairs(B, polys, 1.0):
        if cols[i] != cols[j]:
            continue
        lam = lat(B, ab)
        Q = [vadd(v, lam) for v in polys[j]]
        M2 = poly_maxd2(polys[i], Q)
        if M2 <= 1:
            continue
        if i == j and ab == (0, 0):
            m2 = fmpq(0)
        else:
            m2 = poly_mind2(polys[i], Q)
        if m2 >= 1:
            continue
        tasks.append((i, j, ab, m2))
    return tasks


_G = {}


def run_task(t, split):
    i, j, ab, m2 = t
    B, polys = _G['B'], _G['polys']
    lam = lat(B, ab)
    Q = [vadd(v, lam) for v in polys[j]]
    stats = {}
    if split == 'plus' or m2 <= fmpq(1, 4):
        I = pair_integral(polys[i], Q, '+', stats)
        I2 = None
    else:
        I = pair_integral(polys[i], Q, '-', stats)
        I2 = pair_integral(polys[i], Q, '+', stats) if split == 'both' else None
    return I, I2, stats


def _worker(args):
    chunk, split, prec = args
    ctx.prec = prec
    out = []
    for t in chunk:
        I, I2, st = run_task(t, split)
        enc = lambda x: None if x is None else (str(arb_lo_q(x)), str(arb_hi_q(x)))
        out.append((t[0], t[1], t[2], enc(I), enc(I2), st))
    return out


def certify(D, workers=1, prec=128, max_colours=6, split='auto', verbose=True):
    ctx.prec = prec
    t0 = time.time()
    B, polys, cols, covol = load_map(D, max_colours)
    nd = check_tiling(B, polys)
    if verbose:
        print('input OK: %d convex pieces, %d colours, covolume %s (%.9f); %d nearby translate pairs interior-disjoint'
              % (len(polys), len(set(cols)), covol, float(covol), nd), flush=True)
    tasks = build_tasks(B, polys, cols)
    if verbose:
        print('%d ordered same-colour (i, j, lambda) with min dist < 1 < max dist' % len(tasks), flush=True)
    _G['B'], _G['polys'] = B, polys
    # balance: sort by size
    tasks.sort(key=lambda t: -len(polys[t[0]]) * len(polys[t[1]]))
    chunks = [tasks[w::max(workers, 1)] for w in range(max(workers, 1))]
    if workers > 1:
        import multiprocessing as mp
        with mp.get_context('fork').Pool(workers) as pool:
            res = pool.map(_worker, [(ch, split, prec) for ch in chunks])
    else:
        res = [_worker((chunks[0], split, prec))]
    total = arb(0)
    nedge = nint = 0
    maxdisc = 0.0
    per = []
    dec = lambda e: arb(fmpq(Fraction(e[0]).numerator, Fraction(e[0]).denominator)).union(
        arb(fmpq(Fraction(e[1]).numerator, Fraction(e[1]).denominator)))
    for r in res:
        for (i, j, ab, e, e2, st) in r:
            I = dec(e)
            total += I
            nedge += st.get('nedge', 0)
            nint += st.get('nint', 0)
            per.append((i, j, ab, I))
            if e2 is not None:
                I2 = dec(e2)
                if not I.overlaps(I2):
                    raise AssertionError('log+ and log- formulas disagree on pair %s: %s vs %s' % ((i, j, ab), I, I2))
                maxdisc = max(maxdisc, abs(float((I - I2).mid())))
    p = total / (2 * arb.pi() * arb(covol))
    if verbose:
        print('edge pairs %d, rigorous sub-integrals %d, time %.1fs' % (nedge, nint, time.time() - t0))
        if split == 'both':
            print('log+/log- cross-check: all overlapping, max |mid difference| %.3g' % maxdisc)
        print('p in', p.str(20, radius=True))
    return p, per


def ap_v_from_e(e):
    """smallest v with (29/4)^(1/3) v^(4/3) >= e  <=>  29 v^4 >= 4 e^3  (Agoston-Palvolgyi), exact integers"""
    v = int((4 * e ** 3 / 29) ** 0.25) - 5
    v = max(v, 1)
    while 29 * v ** 4 < 4 * e ** 3:
        v += 1
    assert 29 * v ** 4 >= 4 * e ** 3 and 29 * (v - 1) ** 4 < 4 * e ** 3
    return v


def corollary(p):
    ph = arb_hi_q(p)                      # exact rational >= p
    inv = Fraction(int(ph.q), int(ph.p))
    e = -((-inv.numerator) // inv.denominator)       # ceil(1/ph)
    # e >= 1/p >= 1/ph  ->  e_7 >= ceil(1/ph)
    v = ap_v_from_e(e)
    return ph, e, v


# ------------------------------------------------------------------ self-tests (known exact answers)
def selftest(prec=128):
    ctx.prec = prec
    ok = True
    def S(x): return str(x)
    # T1: unit-square lattice, one colour: p = 1 exactly
    D = {'B': [[1, 0], [0, 1]], 'polys': [[[0, 0], [1, 0], [1, 1], [0, 1]]], 'cols': [0]}
    p, _ = certify(D, verbose=False, prec=prec)
    print('T1 constant colouring of Z^2 (expect 1):', p.str(15, radius=True)); ok &= p.contains(1) and p.rad() < 1e-20
    # T1b: same, but the square cut into 2 triangles, and a non-trivial lattice basis
    D = {'B': [[1, 0], [3, 1]], 'polys': [[[0, 0], [1, 0], [1, 1]], [[0, 0], [1, 1], [0, 1]]], 'cols': [0, 0]}
    p, _ = certify(D, verbose=False, prec=prec)
    print('T1b constant colouring, 2 triangles, skew basis (expect 1):', p.str(15, radius=True)); ok &= p.contains(1) and p.rad() < 1e-20
    # T2: 9-colouring by squares of side s in a 3x3 pattern; s = 3/4: only same-square pairs
    for s in (fmpq(3, 4), fmpq(7, 10)):
        polys, cols = [], []
        for a in range(3):
            for b in range(3):
                polys.append([[S(a * s), S(b * s)], [S((a + 1) * s), S(b * s)], [S((a + 1) * s), S((b + 1) * s)], [S(a * s), S((b + 1) * s)]])
                cols.append(3 * a + b)
        D = {'B': [[S(3 * s), '0'], ['0', S(3 * s)]], 'polys': polys, 'cols': cols}
        p, _ = certify(D, verbose=False, max_colours=9, prec=prec, split='both')
        sa = arb(s)
        a_, b_ = sa.acos(), sa.asin()
        if s * s * 2 > 1:
            I = 4 * (sa * sa * (b_ - a_) - sa * (a_.cos() - b_.cos()) - sa * (b_.sin() - a_.sin()) + (b_.sin() ** 2 - a_.sin() ** 2) / 2)
        else:
            I = arb(0)
        exact = I / (2 * arb.pi() * sa * sa)
        print('T2 9-colour squares s=%s: p =' % s, p.str(15, radius=True), ' closed form', exact.str(15, radius=True))
        ok &= p.overlaps(exact) and p.rad() < 1e-20
    # T3: s = 3/5 -> proper colouring, p = 0
    s = fmpq(3, 5)
    polys, cols = [], []
    for a in range(3):
        for b in range(3):
            polys.append([[S(a * s), S(b * s)], [S((a + 1) * s), S(b * s)], [S((a + 1) * s), S((b + 1) * s)], [S(a * s), S((b + 1) * s)]])
            cols.append(3 * a + b)
    D = {'B': [[S(3 * s), '0'], ['0', S(3 * s)]], 'polys': polys, 'cols': cols}
    p, _ = certify(D, verbose=False, max_colours=9, prec=prec)
    print('T3 proper 9-colouring (expect 0):', p.str(15, radius=True)); ok &= p.contains(0) and p.rad() < 1e-30
    # T4: two colours, stripes of width w on Z^2 (period 2w): p computable 1D:
    # P[same stripe colour]: x uniform mod 2w, direction: displacement dx = cos t; colour same iff floor((x+dx)/w) even diff
    w = fmpq(2, 3)
    D = {'B': [[S(2 * w), '0'], ['0', '1']], 'polys': [[['0', '0'], [S(w), '0'], [S(w), '1'], ['0', '1']],
                                                     [[S(w), '0'], [S(2 * w), '0'], [S(2 * w), '1'], [S(w), '1']]], 'cols': [0, 1]}
    p, _ = certify(D, verbose=False, prec=prec, split='both')
    # exact: for displacement d = |cos t| in [0,1], prob(same) = g(d) with period-2w triangle wave:
    # g(d) = 1 - d/w for d <= w, (d - w)/w for w <= d <= 2w.   w = 2/3: d in [0,1] -> second branch up to 1 <= 4/3
    # p = (2/pi) int_0^{pi/2} g(cos t) dt
    t0 = arb(w).acos()
    pex = (2 / arb.pi()) * ((arb.pi() / 2 - t0) - (1 - t0.sin()) / arb(w)  # int_{t0}^{pi/2} (1 - cos/w)
                             + (t0.sin()) / arb(w) - t0)                # int_0^{t0} (cos - w)/w = sin t0/w - t0
    print('T4 stripes w=2/3 (2 colours): p =', p.str(15, radius=True), ' closed form', pex.str(15, radius=True))
    ok &= p.overlaps(pex) and p.rad() < 1e-20
    print('SELFTEST', 'PASSED' if ok else 'FAILED')
    return ok


# ------------------------------------------------------------------ definition-level Monte Carlo (float, NOT rigorous)
def monte_carlo(D, N, seed=1, chunk=1_000_000, G=1024):
    """random point x in the torus, random direction t, colour(x) == colour(x + u_t) ?  Float sanity check only."""
    import numpy as np
    f = lambda q: float(Fraction(q) if isinstance(q, str) else q)
    B = np.array([[f(x) for x in r] for r in D['B']])
    Binv = np.linalg.inv(B)          # rows are basis vectors: point = u @ B
    polys = []
    for P in D['polys']:
        Q = np.array([[f(x), f(y)] for x, y in P])
        a = np.sum(Q[:, 0] * np.roll(Q[:, 1], -1) - Q[:, 1] * np.roll(Q[:, 0], -1))
        polys.append(Q if a > 0 else Q[::-1])
    cols = np.array(D['cols'])
    # candidate (piece, lattice shift) per grid cell of the fundamental parallelogram (in u-coordinates)
    cand = [[[] for _ in range(G)] for _ in range(G)]
    for i, Q in enumerate(polys):
        U = Q @ Binv                 # u-coords of vertices
        for a in range(int(np.floor(-U[:, 0].max())) - 1, int(np.ceil(-U[:, 0].min())) + 2):
            for b in range(int(np.floor(-U[:, 1].max())) - 1, int(np.ceil(-U[:, 1].min())) + 2):
                V = U + np.array([a, b])
                lo, hi = V.min(0), V.max(0)
                if hi[0] <= 0 or hi[1] <= 0 or lo[0] >= 1 or lo[1] >= 1:
                    continue
                for gx in range(max(0, int(lo[0] * G) - 1), min(G, int(hi[0] * G) + 2)):
                    for gy in range(max(0, int(lo[1] * G) - 1), min(G, int(hi[1] * G) + 2)):
                        cand[gx][gy].append((i, a, b))
    single = np.full((G, G), -1)
    for gx in range(G):
        for gy in range(G):
            cs = set(cols[i] for (i, a, b) in cand[gx][gy])
            if len(cs) == 1:
                single[gx, gy] = cs.pop()
    allc = sorted(set(t for row in cand for cell in row for t in cell))
    def colour(Pt):
        U = Pt @ Binv
        U -= np.floor(U)
        gx = np.minimum((U[:, 0] * G).astype(int), G - 1)
        gy = np.minimum((U[:, 1] * G).astype(int), G - 1)
        c = single[gx, gy].copy()
        idx = np.nonzero(c < 0)[0]
        X = U[idx] @ B
        ca = np.full(len(idx), -1)
        for (i, a, b) in allc:
            Q = polys[i] + a * B[0] + b * B[1]
            e = np.roll(Q, -1, 0) - Q
            ins = np.ones(len(idx), bool)
            for k in range(len(Q)):
                ins &= e[k, 0] * (X[:, 1] - Q[k, 1]) - e[k, 1] * (X[:, 0] - Q[k, 0]) >= 0
            ca[ins] = cols[i]
        c[idx] = ca
        return c
    rng = np.random.default_rng(seed)
    hits = 0
    done = 0
    while done < N:
        n = min(chunk, N - done)
        X = rng.random((n, 2)) @ B
        t = rng.random(n) * 2 * np.pi
        Y = X + np.stack([np.cos(t), np.sin(t)], 1)
        hits += int(np.sum(colour(X) == colour(Y)))
        done += n
    p = hits / N
    return p, math.sqrt(max(p, 1.0 / N) * (1 - p) / N), hits


# ------------------------------------------------------------------ negative tests on a real map
def negtests(D0, workers=4, prec=128):
    import copy
    ctx.prec = prec
    res = []
    def expect_reject(name, D, **kw):
        try:
            certify(D, workers=workers, prec=prec, verbose=False, **kw)
            print('  FAIL (accepted):', name); res.append(False)
        except Rejected as ex:
            print('  rejected as expected: %-48s -> %s' % (name, ex)); res.append(True)
    p0, _ = certify(D0, workers=workers, prec=prec, verbose=False)
    print('baseline p =', p0.str(15, radius=True))
    # 1. float coordinate
    D = copy.deepcopy(D0); D['polys'][0][0][0] = float(Fraction(D['polys'][0][0][0])); expect_reject('float coordinate', D)
    # 2. one vertex of a large piece pushed outward / inward by 1e-6 (breaks tiling)
    big = max(range(len(D0['polys'])), key=lambda i: len(D0['polys'][i]))
    for sgn, name in ((1, 'vertex moved +1e-6 in x'), (-1, 'vertex moved -1e-6 in x')):
        D = copy.deepcopy(D0)
        v = D['polys'][big][2]
        v[0] = str(Fraction(v[0]) + sgn * Fraction(1, 10 ** 6))
        expect_reject(name, D)
    # 3. non-convex: swap two consecutive vertices of the large piece
    D = copy.deepcopy(D0); P = D['polys'][big]; P[1], P[2] = P[2], P[1]; expect_reject('two vertices swapped (non-convex)', D)
    # 4. a seventh colour
    D = copy.deepcopy(D0); D['cols'][0] = max(D0['cols']) + 1; expect_reject('seventh colour', D)
    # 5. piece dropped (area deficit)
    D = copy.deepcopy(D0); del D['polys'][-1]; del D['cols'][-1]; expect_reject('piece deleted', D)
    # 6. piece duplicated (overlap / area excess)
    D = copy.deepcopy(D0); D['polys'].append(D['polys'][0]); D['cols'].append(D['cols'][0]); expect_reject('piece duplicated', D)
    # 7. lattice changed slightly (area mismatch / overlap)
    D = copy.deepcopy(D0); D['B'][1][1] = str(Fraction(D['B'][1][1]) * Fraction(1000001, 1000000)); expect_reject('lattice stretched 1e-6', D)
    # 8. colour relabelling (permutation): p unchanged exactly
    D = copy.deepcopy(D0); perm = {c: (c + 1) % 6 for c in range(6)}; D['cols'] = [perm[c] for c in D['cols']]
    p, _ = certify(D, workers=workers, prec=prec, verbose=False)
    ok = p.overlaps(p0); print('  colour permutation: p =', p.str(15, radius=True), 'same' if ok else 'DIFFERENT'); res.append(ok)
    # 9. recolour one piece with another colour: valid input, p must increase; MC must agree
    D = copy.deepcopy(D0); i0 = big; D['cols'][i0] = (D0['cols'][i0] + 1) % 6
    p, _ = certify(D, workers=workers, prec=prec, verbose=False)
    mc, se, h = monte_carlo(D, 4_000_000, seed=7)
    ok = p > p0 and abs(mc - float(p.mid())) < 4 * se
    print('  recolour piece %d: p = %s (> baseline: %s); MC 4e6 = %.4e +- %.1e  %s' % (i0, p.str(10, radius=True), p > p0, mc, se, 'agree' if ok else 'DISAGREE')); res.append(ok)
    # 10. merge all colours into one: p must be exactly 1 (tests completeness of lattice sums + every pair integral)
    D = copy.deepcopy(D0); D['cols'] = [0] * len(D['cols'])
    t = time.time(); p, _ = certify(D, workers=workers, prec=prec, verbose=False)
    ok = p.contains(1) and p.rad() < 1e-15
    print('  all pieces one colour: p = %s (expect exactly 1) [%.0fs]' % (p.str(18, radius=True), time.time() - t)); res.append(ok)
    # 11. merge two colour classes: p_merged = p0 + 2 X_ab; check p_merged > p0 and MC agreement
    D = copy.deepcopy(D0); D['cols'] = [0 if c == 1 else c for c in D['cols']]
    p, _ = certify(D, workers=workers, prec=prec, verbose=False)
    mc, se, h = monte_carlo(D, 4_000_000, seed=11)
    ok = p > p0 and abs(mc - float(p.mid())) < 4 * se
    print('  colours 0,1 merged: p = %s; MC 4e6 = %.4e +- %.1e  %s' % (p.str(10, radius=True), mc, se, 'agree' if ok else 'DISAGREE')); res.append(ok)
    # 12. uniform rational rescaling by r (valid tiling, equivalent to unit distance 1/r): smooth change
    for r in (Fraction(1001, 1000), Fraction(999, 1000)):
        D = copy.deepcopy(D0)
        sc = lambda q: str(Fraction(q) * r)
        D['B'] = [[sc(x) for x in row] for row in D['B']]
        D['polys'] = [[[sc(x), sc(y)] for x, y in P] for P in D['polys']]
        p, _ = certify(D, workers=workers, prec=prec, verbose=False)
        print('  scaled by %s: p = %s  (ratio to baseline %.4f)' % (r, p.str(10, radius=True), float((p / p0).mid())))
    print('NEGTESTS', 'PASSED' if all(res) else 'FAILED', '(%d/%d)' % (sum(res), len(res)))
    return all(res)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('map', nargs='?')
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--prec', type=int, default=128)
    ap.add_argument('--max-colours', type=int, default=6)
    ap.add_argument('--split', default='auto', choices=['auto', 'plus', 'both'])
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--negtest', action='store_true')
    ap.add_argument('--mc', type=int, default=0, help='also run a float Monte Carlo with this many samples')
    a = ap.parse_args()
    if a.selftest:
        sys.exit(0 if selftest(a.prec) else 1)
    D = json.load(open(a.map))
    if a.negtest:
        sys.exit(0 if negtests(D, workers=min(a.workers, 4), prec=a.prec) else 1)
    try:
        p, per = certify(D, workers=min(a.workers, 4), prec=a.prec, max_colours=a.max_colours, split=a.split)
    except Rejected as ex:
        print('REJECTED:', ex)
        sys.exit(2)
    ph, e, v = corollary(p)
    print('p_hi (exact rational upper bound) ~ %.10e   1/p_hi ~ %.6f' % (float(ph), float(1 / ph)))
    print('=> every 7-chromatic unit-distance graph has e >= %d edges and (Agoston-Palvolgyi) v >= %d vertices' % (e, v))
    if a.mc:
        t = time.time()
        mc, se, h = monte_carlo(D, a.mc)
        print('float Monte Carlo (%d samples, %d mono, %.0fs): p ~ %.4e +- %.1e  (rigorous mid %.6e, %.1f sigma)'
              % (a.mc, h, time.time() - t, mc, se, float(p.mid()), (mc - float(p.mid())) / se))
