"""Rigorous upper/lower bounds on p = P(random unit segment is monochromatic) for a periodic
colouring of the plane given by exact-rational convex polygons.

usage:  python3 certify.py colouring.json [prec_bits]

JSON: {"B": [[x,y],[x,y]],                 period lattice basis (rationals as strings "a/b")
       "polys": [[[x,y],...], ...],        convex polygons (any orientation), one rep each
       "cols": [c0, c1, ...]}              colour of each polygon

Checks (exact rational arithmetic, python-flint fmpq):
  * every polygon strictly convex;
  * the polygons' lattice translates have pairwise disjoint interiors (separating axis test);
  * sum of areas == covolume  => translates tile the plane up to a null set.
Then  p = (1/(2 pi covol)) * sum_{i,j same colour} sum_lam  I(i,j,lam),
      I(i,j,lam) = int_0^{2pi} area(P_i cap (P_j + lam - u_theta)) dtheta.
Each I is enclosed with arb ball arithmetic: theta-breakpoints where a vertex of one polygon
meets an edge-line of the other (complete superset of the non-smooth points; on each arc in
between the area is a quadratic polynomial of u = (cos t, sin t), i.e. a trigonometric
polynomial of degree 2), exact fit of that trig polynomial from 5 rigorous point evaluations
(+1 consistency check), exact integration; breakpoint balls bounded by [0, min area] * width.
Only pairs with min dist <= 1 <= max dist (exact) can contribute; others are skipped.
"""
import sys, json, math, time
from flint import fmpq, fmpz, arb, arb_mat, ctx


def Q(s):
    if isinstance(s, str):
        if '/' in s:
            a, b = s.split('/')
            return fmpq(int(a), int(b))
        return fmpq(int(s))
    if isinstance(s, int):
        return fmpq(s)
    raise ValueError('coordinates must be int or "a/b" strings: %r' % (s,))


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


def area2(P):
    return sum(cross(P[k], P[(k + 1) % len(P)]) for k in range(len(P)))


def make_ccw(P):
    a = area2(P)
    if a == 0:
        raise ValueError('degenerate polygon')
    return P if a > 0 else P[::-1]


def check_convex(P):
    n = len(P)
    for k in range(n):
        if cross(sub(P[(k + 1) % n], P[k]), sub(P[(k + 2) % n], P[(k + 1) % n])) <= 0:
            return False
    return True


def hp(P):
    """edges: list of (a, d, n, c): start, direction, outward normal (unnormalised), offset"""
    out = []
    n = len(P)
    for k in range(n):
        a = P[k]
        d = sub(P[(k + 1) % n], a)
        nn = (d[1], -d[0])
        out.append((a, d, nn, dot(nn, a)))
    return out


def separated(P, R):
    """interiors disjoint (convex polygons) -- exact separating axis test"""
    for poly_a, poly_b in ((P, R), (R, P)):
        for (a, d, n, c) in hp(poly_a):
            if min(dot(n, v) for v in poly_b) >= c:
                return True
    return False


def seg_pt_d2(p, a, b):
    d = sub(b, a)
    dd = dot(d, d)
    t = dot(sub(p, a), d) / dd
    if t < 0:
        t = fmpq(0)
    elif t > 1:
        t = fmpq(1)
    q = (a[0] + t * d[0], a[1] + t * d[1])
    w = sub(p, q)
    return dot(w, w)


def inside(p, P):
    return all(dot(n, p) <= c for (a, d, n, c) in hp(P))


def min_d2(P, R):
    if not separated(P, R):
        return fmpq(0)
    best = None
    for A, Bp in ((P, R), (R, P)):
        m = len(Bp)
        for v in A:
            for k in range(m):
                x = seg_pt_d2(v, Bp[k], Bp[(k + 1) % m])
                if best is None or x < best:
                    best = x
    return best


def max_d2(P, R):
    return max(dot(sub(v, w), sub(v, w)) for v in P for w in R)


# ---------------------------------------------------------------- arb part
def area_at(P, R, ux, uy, hpP, hpR):
    """enclosure of area(P cap (R - u)) for arb ux, uy"""
    zero = arb(0)
    one = arb(1)
    tot = arb(0)
    # edges of P clipped by R - u : n.y <= c - n.u
    for (a, d, _, _) in hpP:
        lo, hi = zero, one
        for (_, _, n, c) in hpR:
            q = dot(n, d)
            r = (c - dot(n, a)) - (n[0] * ux + n[1] * uy)
            if q > 0:
                hi = hi.min(r / q)
            elif q < 0:
                lo = lo.max(r / q)
            else:
                if r < 0:
                    hi = arb(-1)
                elif not (r > 0):
                    raise ArithmeticError('ambiguous parallel constraint')
        w = (hi - lo).max(zero)
        tot += w * cross(a, d)
    # edges of R - u clipped by P: n.(a - u + t d) <= c
    for (a, d, _, _) in hpR:
        lo, hi = zero, one
        for (_, _, n, c) in hpP:
            q = dot(n, d)
            r = (c - dot(n, a)) + (n[0] * ux + n[1] * uy)
            if q > 0:
                hi = hi.min(r / q)
            elif q < 0:
                lo = lo.max(r / q)
            else:
                if r < 0:
                    hi = arb(-1)
                elif not (r > 0):
                    raise ArithmeticError('ambiguous parallel constraint')
        w = (hi - lo).max(zero)
        tot += w * (cross(a, d) - (ux * d[1] - uy * d[0]))
    return tot / 2


def events(P, R, hpP, hpR, PI2):
    """arb balls of all theta in [0,2pi) where a vertex of P lies on an edge line of R - u
    or a vertex of R - u lies on an edge line of P."""
    ev = []
    eqs = []
    for v in P:
        for (_, _, n, c) in hpR:
            eqs.append((n, c - dot(n, v)))        # n.u = rho
    for w in R:
        for (_, _, n, c) in hpP:
            eqs.append((n, dot(n, w) - c))
    seen = set()
    for (n, rho) in eqs:
        key = (n[0], n[1], rho)  # fmpq hashable
        if key in seen:
            continue
        seen.add(key)
        nn2 = dot(n, n)
        if rho * rho > nn2:
            continue
        phi = arb.atan2(arb(n[1]), arb(n[0]))
        if rho * rho == nn2:
            ths = [phi if rho > 0 else phi + arb.pi()]
        else:
            al = (arb(rho) / arb(nn2).sqrt()).acos()
            ths = [phi + al, phi - al]
        for t in ths:
            # reduce mod 2pi (t is in (-2pi, 3pi))
            for _ in range(3):
                if t < 0:
                    t = t + PI2
                elif t > PI2:
                    t = t - PI2
            ev.append(t)
    return ev


def perim(P):
    return sum(arb(dot(sub(P[(k + 1) % len(P)], P[k]), sub(P[(k + 1) % len(P)], P[k]))).sqrt() for k in range(len(P)))


def integrate_pair(P, R, chk=True):
    PI2 = 2 * arb.pi()
    hpP, hpR = hp(P), hp(R)
    Amax = min(area2(P), area2(R)) / 2
    Lip = min(perim(P), perim(R)) / 2
    ev = events(P, R, hpP, hpR, PI2)
    ev.append(arb(0))
    ev.append(PI2)
    iv = sorted([(e.lower(), e.upper()) for e in ev], key=lambda z: float(z[0].mid()))
    # merge overlapping balls into clusters [lo, hi]
    cl = []
    for lo, hi in iv:
        if cl and not (lo > cl[-1][1]):
            cl[-1][1] = cl[-1][1].max(hi)
        else:
            cl.append([lo, hi])
    total = arb(0)
    nfit = 0
    # cluster contributions (only parts inside [0, 2pi])
    for lo, hi in cl:
        lo2 = lo.max(arb(0))
        hi2 = hi.min(PI2)
        w = (hi2 - lo2).max(arb(0))
        total += arb(0).union(Amax * w)
    for k in range(len(cl) - 1):
        a = cl[k][1]
        b = cl[k + 1][0]
        if a > PI2 or b < 0:
            continue
        W = b - a
        if not (W > 0):
            continue
        if W < arb(10) ** (-4):
            # small cell: midpoint value +- Lipschitz bound (|d area/d theta| <= min perimeter / 2)
            tm = (a + b) / 2
            fm = area_at(P, R, tm.cos(), tm.sin(), hpP, hpR)
            Iab = W * fm + arb(0, 1) * Lip * W * W / 4
            total += Iab
            continue
        # 5 Chebyshev nodes in (a, b); local variable tau = theta - mid
        mid = (a + b) / 2
        xs = [-arb.cos(arb.pi() * (2 * s + 1) / 10) / 2 for s in range(5)]   # in (-1/2, 1/2)
        rows = []
        vals = []
        for x in xs:
            tau = W * x
            t = mid + tau
            c1, s1 = tau.cos(), tau.sin()
            c2, s2 = (2 * tau).cos(), (2 * tau).sin()
            rows += [arb(1), c1, s1, c2, s2]
            vals.append(area_at(P, R, t.cos(), t.sin(), hpP, hpR))
        A = arb_mat(5, 5, rows)
        y = arb_mat(5, 1, vals)
        co = A.solve(y)
        c0, a1, b1, a2, b2 = [co[i, 0] for i in range(5)]
        if chk:
            tau = W * arb(fmpq(-13, 100))
            t = mid + tau
            fm = area_at(P, R, t.cos(), t.sin(), hpP, hpR)
            gm = c0 + a1 * tau.cos() + b1 * tau.sin() + a2 * (2 * tau).cos() + b2 * (2 * tau).sin()
            if not fm.overlaps(gm):
                raise AssertionError('trig-poly fit inconsistent: missing breakpoint?')
        Iab = c0 * W + a1 * 2 * (W / 2).sin() + a2 * W.sin()
        total += Iab
        nfit += 1
    return total, nfit


def load(fn):
    D = json.load(open(fn))
    B = [tuple(Q(x) for x in row) for row in D['B']]
    polys = [make_ccw([tuple(Q(x) for x in v) for v in P]) for P in D['polys']]
    cols = D['cols']
    return B, polys, cols


def lattice_vectors(B, rad):
    # all a b1 + b b2 with |.| <= rad (float search with margin)
    b1 = [float(x) for x in B[0]]
    b2 = [float(x) for x in B[1]]
    det = abs(b1[0] * b2[1] - b1[1] * b2[0])
    R = int(rad * max(math.hypot(*b1), math.hypot(*b2)) / det) + 2
    out = []
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            x = a * b1[0] + b * b2[0]
            y = a * b1[1] + b * b2[1]
            if math.hypot(x, y) <= rad + 1e-6:
                out.append((a, b))
    return out


_CTX = {}


def _worker(args):
    fn, prec, chunk = args
    ctx.prec = prec
    tasks, polys = _CTX['tasks'], _CTX['polys']
    tot = arb(0)
    nf = 0
    for ti in chunk:
        (i, j, ab, Rj, mult) = tasks[ti]
        I, k = integrate_pair(polys[i], Rj)
        nf += k
        tot += mult * I
    lo, hi = tot.lower(), tot.upper()
    lm, le = lo.mid().man_exp()
    hm, he = hi.mid().man_exp()
    return (int(lm), int(le), int(hm), int(he), nf)


def certify(fn, prec=128, verbose=True):
    ctx.prec = prec
    t0 = time.time()
    B, polys, cols = load(fn)
    covol = abs(cross(B[0], B[1]))
    for i, P in enumerate(polys):
        if not check_convex(P):
            raise ValueError('polygon %d not strictly convex' % i)
    S = sum(area2(P) for P in polys) / 2
    if S != covol:
        raise ValueError('areas %s != covolume %s' % (S, covol))
    cen = [(sum(float(v[0]) for v in P) / len(P), sum(float(v[1]) for v in P) / len(P)) for P in polys]
    rad = [max(math.hypot(float(v[0]) - c[0], float(v[1]) - c[1]) for v in P) for P, c in zip(polys, cen)]
    rmax = max(rad)
    # tiling disjointness
    LV = lattice_vectors(B, 2 * rmax + 2 + 1e-9 + max(math.hypot(*c) for c in cen) * 2)
    def tr(P, ab):
        lam = (ab[0] * B[0][0] + ab[1] * B[1][0], ab[0] * B[0][1] + ab[1] * B[1][1])
        return [add(v, lam) for v in P], lam
    ndis = 0
    for i in range(len(polys)):
        for j in range(i, len(polys)):
            for ab in LV:
                if i == j and ab == (0, 0):
                    continue
                Rj, lam = tr(polys[j], ab)
                cj = (cen[j][0] + float(lam[0]), cen[j][1] + float(lam[1]))
                if math.hypot(cen[i][0] - cj[0], cen[i][1] - cj[1]) > rad[i] + rad[j] + 1e-9:
                    continue
                if not separated(polys[i], Rj):
                    raise ValueError('polygons %d and %d+%s overlap' % (i, j, ab))
                ndis += 1
    if verbose:
        print('tiling verified: %d polys, covolume %s (~%.6f), %d close pairs disjoint'
              % (len(polys), covol, float(covol), ndis), flush=True)
    # same-colour pairs
    tasks = []
    for i in range(len(polys)):
        for j in range(len(polys)):
            if cols[i] != cols[j]:
                continue
            for ab in LV:
                # symmetry: (i,j,lam) ~ (j,i,-lam); keep canonical rep
                key, mkey = (i, j, ab), (j, i, (-ab[0], -ab[1]))
                if mkey < key:
                    continue
                Rj, lam = tr(polys[j], ab)
                cj = (cen[j][0] + float(lam[0]), cen[j][1] + float(lam[1]))
                dc = math.hypot(cen[i][0] - cj[0], cen[i][1] - cj[1])
                if dc > rad[i] + rad[j] + 1.0 + 1e-6:
                    continue
                if max_d2(polys[i], Rj) < 1:
                    continue
                if min_d2(polys[i], Rj) > 1:
                    continue
                mult = 1 if key == mkey else 2
                tasks.append((i, j, ab, Rj, mult))
    _CTX['tasks'] = tasks
    _CTX['polys'] = polys
    if verbose:
        print('%d contributing pair classes' % len(tasks), flush=True)
    total = arb(0)
    nf = 0
    workers = int(__import__('os').environ.get('CERT_WORKERS', '1'))
    if workers <= 1:
        for (i, j, ab, Rj, mult) in tasks:
            I, k = integrate_pair(polys[i], Rj)
            nf += k
            total += mult * I
    else:
        import multiprocessing as mp
        jobs = [(fn, prec, ti) for ti in range(len(tasks))]
        chunks = [list(range(w, len(tasks), workers)) for w in range(workers)]
        with mp.get_context('fork').Pool(workers) as pool:
            res = pool.map(_worker, [(fn, prec, ch) for ch in chunks])
        for (lo_m, lo_e, hi_m, hi_e, k) in res:
            nf += k
            lo = arb(fmpz(lo_m)) * arb(2) ** lo_e
            hi = arb(fmpz(hi_m)) * arb(2) ** hi_e
            total += lo.union(hi)
    p = total / (2 * arb.pi() * arb(covol))
    if verbose:
        print('cells fitted: %d   time %.1fs' % (nf, time.time() - t0))
        print('p in', p.str(20, radius=True))
        print('p_hi =', p.upper().str(20), '  1/p_hi =', (1 / p.upper()).str(15))
    return p


if __name__ == '__main__':
    prec = int(sys.argv[2]) if len(sys.argv) > 2 else 160
    p = certify(sys.argv[1], prec)
    import bounds
    from fractions import Fraction
    ph = p.upper()
    # exact rational slightly above p_hi
    ph_q = Fraction(float(ph.mid())) + Fraction(1, 10 ** 15)
    assert arb(fmpq(ph_q.numerator, ph_q.denominator)) >= ph
    e = math.ceil(1 / ph_q)
    print('implied: e >= %d,  v >= %d   (for k = number of colours + 1)' % (e, bounds.v_from_e(e)))
