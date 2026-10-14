#!/usr/bin/env python3
"""Independent certifier for an Erdos #188 periodic red/blue colouring.

Colouring: P = lattice spanned by b1, b2 (rational).  RED = union of OPEN discs of
radius r (rational, r <= 1/2) centred at c_i + P (rational centres).  BLUE = rest.

(a) unit-distance-freeness (exact rational arithmetic):
    every pair of distinct lifted centres is at distance >= 1 + 2r.  Then two points
    in one open disc are at distance < 2r <= 1, and two points in different open
    discs are at distance > |c - c'| - 2r >= 1.  So no red unit distance.

(b) every unit-step k-AP {x + j u : 0 <= j < k}, |u| = 1, meets RED.
    * Directions: u ranges over the half circle theta in [0, pi] (u and -u give the
      same family of APs).  We use rational unit vectors u_m = ((1-t^2)/(1+t^2),
      2t/(1+t^2)), t = tan(theta_m/2) rounded to a dyadic rational, and assign to
      u_m the arc [u_m, u_{m+1}].  Every u on that arc has |u - u_m| <= e_m :=
      |u_{m+1} - u_m| (rounded up), so the j-th AP point moves by <= j e_m.  Hence
      it suffices that for all x:  exists j<k with x + j u_m in D(c, r - j e_m) for
      some lifted centre c  ("eroded discs").
    * Starts x range over the closed fundamental parallelogram F = {a b1 + b b2 :
      a, b in [0,1]} (every x is P-equivalent to a point of F).
    * Coordinates t = x.u_m, s = x.u_m^perp.  F is cut into strips s in [sa, sb].
      For a disc of radius rho centred at (tc, sc), the set of t with (t, s) in the
      disc for EVERY s in [sa, sb] is [tc - h, tc + h], h = sqrt(rho^2 - dlt^2),
      dlt = max(|sa - sc|, |sb - sc|) (convexity).  So start (t0, s) is blocked at
      step j if t0 in [tc - h_j - j, tc + h_j - j].  We check that these intervals
      (over lifted discs and 0<=j<k) cover [Tlo, Thi] = t-range of F within the strip.
    * Floating point: all inputs are rationals of moderate size; every computed
      radius is reduced by MARGIN = 1e-9 and every cover test demands overlap
      >= MARGIN, which dominates float64 rounding (errors ~1e-12 at these
      magnitudes).  Failing strips / arcs are subdivided adaptively.

Usage: python3 certify.py config.json [k]
"""
import sys, json, math
from fractions import Fraction as Fr
import numpy as np

MARGIN = 1e-9

def load(path):
    d = json.load(open(path))
    B = [[Fr(x) for x in row] for row in d['B']]          # B[0] = (b1x, b2x), B[1] = (b1y, b2y)
    b1 = (B[0][0], B[1][0]); b2 = (B[0][1], B[1][1])
    C = [(Fr(c[0]), Fr(c[1])) for c in d['centers']]
    r = Fr(d['r'])
    radii = [Fr(x) for x in d['radii']] if 'radii' in d else [r] * len(C)
    d['_radii'] = radii
    return b1, b2, C, r, d

# ---------------------------------------------------------------- part (a)
def check_unit_distance_free(b1, b2, C, r, radii=None):
    if radii is None: radii = [r] * len(C)
    assert all(0 < x <= Fr(1, 2) for x in radii), 'radii must be in (0, 1/2]'
    A = b1[0] * b2[1] - b1[1] * b2[0]
    assert A != 0
    A = abs(A)
    maxb = max(math.sqrt(float(b1[0] ** 2 + b1[1] ** 2)), math.sqrt(float(b2[0] ** 2 + b2[1] ** 2)))
    worst = None
    n = len(C)
    for i in range(n):
        for j in range(n):
            dx = C[i][0] - C[j][0]; dy = C[i][1] - C[j][1]
            need = (1 + radii[i] + radii[j]) ** 2
            D = math.sqrt(float(dx * dx + dy * dy)) + float(1 + radii[i] + radii[j]) + 1
            K = int(D * maxb / float(A)) + 2      # |a| <= |lam| |b2| / A
            for a in range(-K, K + 1):
                for b in range(-K, K + 1):
                    if i == j and a == 0 and b == 0: continue
                    ex = dx - a * b1[0] - b * b2[0]
                    ey = dy - a * b1[1] - b * b2[1]
                    q = ex * ex + ey * ey - need + 4     # report (dist^2 - need) + 4
                    if worst is None or q < worst: worst = q
                    q = q - 4 + need
                    if q < need:
                        return False, (i, j, a, b, float(q))
    return True, float(worst)

# ---------------------------------------------------------------- part (b)
def _ranges(starts, counts):
    """concatenation of arange(starts[i], starts[i]+counts[i])"""
    counts = np.asarray(counts, np.int64); starts = np.asarray(starts, np.int64)
    tot = int(counts.sum())
    if tot == 0: return np.zeros(0, np.int64)
    off = np.repeat(starts - np.cumsum(np.r_[0, counts[:-1]]), counts)
    return off + np.arange(tot)

class Cert:
    def __init__(self, b1, b2, C, r, k, radii=None):
        self.b1 = np.array([float(b1[0]), float(b1[1])])
        self.b2 = np.array([float(b2[0]), float(b2[1])])
        self.C = np.array([[float(c[0]), float(c[1])] for c in C])
        self.r = float(r); self.k = k
        self.Rad = np.array([float(x) for x in radii]) if radii is not None else np.full(len(C), float(r))
        self.r = float(self.Rad.max())
        self.F = np.array([[0, 0], self.b1, self.b1 + self.b2, self.b2])

    def lifted(self, u, up, tlo, thi, slo, shi):
        """lifted centres with t in [tlo,thi], s in [slo,shi]; returns (t, s) arrays"""
        corners = np.array([t * u + s * up for t in (tlo, thi) for s in (slo, shi)])
        Bm = np.stack([self.b1, self.b2], 1)
        L = np.linalg.solve(Bm, corners.T).T
        a0, a1 = math.floor(L[:, 0].min()) - 2, math.ceil(L[:, 0].max()) + 2
        c0, c1 = math.floor(L[:, 1].min()) - 2, math.ceil(L[:, 1].max()) + 2
        aa, bb = np.meshgrid(np.arange(a0, a1 + 1), np.arange(c0, c1 + 1), indexing='ij')
        shifts = aa.ravel()[:, None] * self.b1 + bb.ravel()[:, None] * self.b2
        P = (self.C[None, :, :] + shifts[:, None, :]).reshape(-1, 2)
        Rl = np.tile(self.Rad, len(shifts))
        t = P @ u; s = P @ up
        m = (t >= tlo) & (t <= thi) & (s >= slo) & (s <= shi)
        return t[m], s[m], Rl[m]

    def strip_trange(self, u, up, sa, sb):
        """t-range of F intersected with slab sa<=s<=sb (vectorised over strips)."""
        Ft = self.F @ u; Fs = self.F @ up
        lo = np.full(len(sa), np.inf); hi = np.full(len(sa), -np.inf)
        for v in range(4):
            inside = (Fs[v] >= sa) & (Fs[v] <= sb)
            lo = np.where(inside, np.minimum(lo, Ft[v]), lo)
            hi = np.where(inside, np.maximum(hi, Ft[v]), hi)
        for v in range(4):
            w = (v + 1) % 4
            for sl in (sa, sb):
                ds = Fs[w] - Fs[v]
                if abs(ds) < 1e-300: continue
                lam = (sl - Fs[v]) / ds
                ok = (lam >= 0) & (lam <= 1)
                tt = Ft[v] + lam * (Ft[w] - Ft[v])
                lo = np.where(ok, np.minimum(lo, tt), lo)
                hi = np.where(ok, np.maximum(hi, tt), hi)
        # outward rounding
        return lo - 1e-9, hi + 1e-9

    def check_dir(self, u, e, w0=0.05, wmin=0.0015):
        """True if every start in F is blocked within k steps for all directions
        within e of u.  Adaptive strip refinement."""
        k = self.k; r = self.r
        up = np.array([-u[1], u[0]])
        Fs = self.F @ up; Ft = self.F @ u
        smin, smax = Fs.min(), Fs.max()
        tmin, tmax = Ft.min(), Ft.max()
        T, S, Rl = self.lifted(u, up, tmin - r - 1, tmax + k + r + 1, smin - r - 1, smax + r + 1)
        order = np.argsort(S); T = T[order]; S = S[order]; Rl = Rl[order]
        rho = (Rl, e)                                  # radius of step-j eroded disc: Rl - j e - MARGIN
        nst = max(1, int(math.ceil((smax - smin) / w0)))
        edges = np.linspace(smin, smax, nst + 1)
        sa = edges[:-1].copy(); sb = edges[1:].copy()
        sa[0] -= 1e-9; sb[-1] += 1e-9
        while len(sa):
            bad = self._check_strips(T, S, rho, u, up, sa, sb)
            if not bad.any(): return True
            w = (sb - sa)[bad]
            if w.min() < wmin: return False
            # split bad strips in half
            a2 = sa[bad]; b2 = sb[bad]; m2 = (a2 + b2) / 2
            sa = np.concatenate([a2, m2]); sb = np.concatenate([m2, b2])
        return True

    def _check_strips(self, T, S, rho, u, up, sa, sb):
        k = self.k
        tlo, thi = self.strip_trange(u, up, sa, sb)
        Rl, e = rho
        r0 = self.r
        i0 = np.searchsorted(S, sa - r0); i1 = np.searchsorted(S, sb + r0)
        cnt = i1 - i0
        sid = np.repeat(np.arange(len(sa)), cnt)
        idx = _ranges(i0, cnt)
        tc = T[idx]; sc = S[idx]; rc = Rl[idx]
        dlt = np.maximum(np.abs(sa[sid] - sc), np.abs(sb[sid] - sc))
        # candidate j: tc - j in [tlo - 1, thi + 1]
        jlo = np.maximum(0, np.floor(tc - thi[sid] - 1)).astype(np.int64)
        jhi = np.minimum(k - 1, np.ceil(tc - tlo[sid] + 1)).astype(np.int64)
        nj = np.maximum(0, jhi - jlo + 1)
        rep = np.repeat(np.arange(len(tc)), nj)
        jj = _ranges(jlo, nj)
        tc2 = tc[rep]; d2 = dlt[rep]; s2 = sid[rep]
        rj = rc[rep] - jj * e - MARGIN
        h2 = rj * rj - d2 * d2
        ok = (h2 > 0) & (rj > 0.01)     # rho >= 0.01 keeps the float error analysis valid
        h = np.sqrt(np.where(ok, h2, 0)) - MARGIN
        ok &= h > 0
        lo = (tc2 - h - jj)[ok]; hi = (tc2 + h - jj)[ok]; s2 = s2[ok]
        # coverage of [tlo, thi] per strip
        nstr = len(sa)
        lo = np.maximum(lo, tlo[s2]); hi = np.minimum(hi, thi[s2])
        keep = hi > lo
        lo, hi, s2 = lo[keep], hi[keep], s2[keep]
        o = np.lexsort((lo, s2)); lo, hi, s2 = lo[o], hi[o], s2[o]
        bad = np.ones(nstr, bool)
        if len(lo) == 0: return bad
        # running max of hi within each strip: work relative to tlo so that the
        # per-strip offset trick stays exact to ~1e-12
        W = float(np.ceil((thi - tlo).max() + 2))
        base = tlo[s2]; span = (thi - tlo)[s2]
        lr = lo - base; hr = hi - base               # relative coords in [0, span]
        shift = s2 * W
        run = np.maximum.accumulate(hr + shift) - shift   # running max (relative), error ~1e-13
        first = np.r_[True, s2[1:] != s2[:-1]]
        prev_run = np.r_[-np.inf, run[:-1]]
        gap = (~first) & (lr > prev_run - MARGIN) & (prev_run < span - 1e-11)
        last = np.r_[s2[1:] != s2[:-1], True]
        endok = np.zeros(nstr, bool); endok[s2[last]] = run[last] >= span[last] - 1e-11
        # lo was clipped at tlo, so lr == 0 exactly iff an interval reaches tlo
        startok = np.zeros(nstr, bool); startok[s2[first]] = lr[first] <= 0.0
        gapany = np.zeros(nstr, bool); np.logical_or.at(gapany, s2[gap], True)
        good = startok & endok & ~gapany
        return ~good

def rational_dirs(dtheta):
    """rational unit vectors with theta from 0 to pi; returns list of (u (Fractions), float u)"""
    M = int(math.ceil(math.pi / dtheta))
    out = []
    for m in range(M + 1):
        th = min(math.pi, m * math.pi / M)
        if m == M:
            out.append((Fr(-1), Fr(0))); continue
        t = Fr(round(math.tan(th / 2) * 2 ** 24), 2 ** 24) if th < math.pi * 0.75 else None
        if t is None:
            # use the reflected parametrisation for theta near pi: u = -((1-t^2)/(1+t^2), -2t/(1+t^2))
            t2 = Fr(round(math.tan((math.pi - th) / 2) * 2 ** 24), 2 ** 24)
            ux = -(1 - t2 * t2) / (1 + t2 * t2); uy = 2 * t2 / (1 + t2 * t2)
        else:
            ux = (1 - t * t) / (1 + t * t); uy = 2 * t / (1 + t * t)
        assert ux * ux + uy * uy == 1
        out.append((ux, uy))
    return out

def arc_bound(ua, ub):
    """rigorous float upper bound for |ua - ub| (Fractions)"""
    q = (ua[0] - ub[0]) ** 2 + (ua[1] - ub[1]) ** 2
    return math.sqrt(float(q)) * (1 + 1e-12) + 1e-15

def certify(path, k, dtheta=0.002, verbose=True, depth=6):
    b1, b2, C, r, d = load(path)
    ok, info = check_unit_distance_free(b1, b2, C, r, d['_radii'])
    print('(a) unit-distance-free:', ok, info, flush=True)
    if not ok: return False
    cert = Cert(b1, b2, C, r, k, d['_radii'])
    dirs = rational_dirs(dtheta)
    stack = [(dirs[m], dirs[m + 1], 0) for m in range(len(dirs) - 1)][::-1]
    ndone = 0; nfail = 0
    while stack:
        ua, ub, dep = stack.pop()
        e = arc_bound(ua, ub)
        u = np.array([float(ua[0]), float(ua[1])])
        if cert.check_dir(u, e):
            ndone += 1
            continue
        if dep >= depth:
            print('FAIL at theta = %.6f deg' % math.degrees(math.atan2(float(ua[1]), float(ua[0]))), flush=True)
            return False
        # split arc at a rational midpoint
        th_a = math.atan2(float(ua[1]), float(ua[0])); th_b = math.atan2(float(ub[1]), float(ub[0]))
        if th_b < th_a: th_b += 2 * math.pi
        tm = (th_a + th_b) / 2
        t = Fr(round(math.tan(tm / 2) * 2 ** 30), 2 ** 30) if abs(tm) < 2.5 else None
        if t is None:
            t2 = Fr(round(math.tan((math.pi - tm) / 2) * 2 ** 30), 2 ** 30)
            um = (-(1 - t2 * t2) / (1 + t2 * t2), 2 * t2 / (1 + t2 * t2))
        else:
            um = ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
        stack.append((um, ub, dep + 1)); stack.append((ua, um, dep + 1))
        nfail += 1
    print('(b) all directions certified for k = %d  (%d arcs, %d splits)' % (k, ndone, nfail), flush=True)
    return True

if __name__ == '__main__':
    import time
    path = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else json.load(open(path))['k']
    dth = float(sys.argv[3]) if len(sys.argv) > 3 else 0.002
    t0 = time.time()
    res = certify(path, k, dtheta=dth)
    print('time %.0f s' % (time.time() - t0))
    print('CERTIFIED' if res else 'NOT CERTIFIED', 'k =', k)
