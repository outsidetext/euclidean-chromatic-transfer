# Fast independent check of Erdos #173 box certificates (same method as box173_check.py, vectorised).
# Rigour: J0 values from fastlib/j0fast with |error| <= J0ERR = 1e-14 per value, added explicitly; Lipschitz
# enclosures with |J0'| = |J1| <= 0.5819; tail t >= T by |J0(x)| <= sqrt(2/(pi x)); coverage check as before.
# Cells of one bisection level are processed together (numpy), so the per-cell Python overhead disappears.
import sys, os, json, itertools, math
from fractions import Fraction as F
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from j0fast import j0 as J0V
J0ERR = 1e-14
L1 = 0.5819
GRID = 0.002


class J0Range:
    """bounds of J0 over [lo, hi] from a grid table (values within J0ERR) plus Lipschitz half-step."""
    def __init__(self, xmax):
        self.n = int(xmax / GRID) + 3
        self.v = J0V(np.arange(self.n) * GRID)
        # sparse table for range max/min over grid indices (O(1) queries)
        self.mx = [self.v]; self.mn = [self.v]; k = 1
        while 2 * k <= self.n:
            a, b = self.mx[-1], self.mn[-1]
            self.mx.append(np.maximum(a[:-k], a[k:])); self.mn.append(np.minimum(b[:-k], b[k:])); k *= 2

    def query(self, lo, hi, upper):
        i0 = np.floor(lo / GRID).astype(np.int64); i1 = np.ceil(hi / GRID).astype(np.int64)
        out = np.empty(lo.shape)
        big = i1 >= self.n
        sm = ~big
        if sm.any():
            a, b = i0[sm], i1[sm]; ln = b - a + 1
            k = np.floor(np.log2(ln)).astype(np.int64)
            res = np.empty(a.shape)
            for kk in np.unique(k):
                m = k == kk; tab = (self.mx if upper else self.mn)[kk]; w = 1 << kk
                x1, x2 = tab[a[m]], tab[b[m] - w + 1]
                res[m] = np.maximum(x1, x2) if upper else np.minimum(x1, x2)
            out[sm] = res + (1 if upper else -1) * (L1 * GRID / 2 + J0ERR + 1e-15)
        if big.any():
            env = np.sqrt(2 / (np.pi * np.maximum(lo[big], 1e-300)))
            out[big] = np.minimum(1.0, env) if upper else -env
        return out


def check(C, JR):
    (a0, a1), (b0, b1) = [[F(x) for x in iv] for iv in C['box']]
    y = [F(x) for x in C['y']]
    L = min(y[i] - y[(i + 1) % 3] - y[(i + 2) % 3] for i in range(3))
    fixed = {F(1): y[2]}; mut = F(0)
    for X in C['aux']:
        r = [F(v) for v in X['r']]; sg = X['sg']; mu = F(X['mu']); assert mu >= 0
        assert min(sg[0]*s[0]*s[1] + sg[1]*s[0]*s[2] + sg[2]*s[1]*s[2] for s in itertools.product((1, -1), repeat=3)) >= -1
        assert all(v > 0 for v in r) and max(r) <= sum(r) - max(r)
        for v, z in zip(r, sg): fixed[v] = fixed.get(v, 0) + mu * z
        mut += mu
    Lam = float(L - mut); assert Lam > 0
    ks = np.array([float(k) for k, c in fixed.items() if c != 0]); cs = np.array([float(c) for k, c in fixed.items() if c != 0])
    T = max(150.0, float(C['T']))
    ya, yb = float(y[0]), float(y[1]); fa0, fa1, fb0, fb1 = map(float, (a0, a1, b0, b1))
    tail = float(np.sum(np.abs(cs) * np.sqrt(2 / (np.pi * ks * T)))) + abs(ya) * math.sqrt(2 / (math.pi * fa0 * T)) + abs(yb) * math.sqrt(2 / (math.pi * fb0 * T))
    assert tail < Lam - 1e-9, ('tail', tail, Lam)
    Lip = float(np.sum(np.abs(cs) * ks)) * L1
    errfix = float(np.sum(np.abs(cs))) * J0ERR + abs(ya) * 0 + 1e-12
    lo = np.linspace(0, T, 4097)[:-1]; hi = lo + T / 4096
    ncell = 0
    while lo.size:
        m = (lo + hi) / 2; rad = (hi - lo) / 2
        vals = np.zeros(lo.size)
        for k, c in zip(ks, cs):
            vals += c * J0V(k * m)
        ub = vals + errfix + Lip * rad
        ub += ya * (JR.query(fa0 * lo, fa1 * hi, ya >= 0))
        ub += yb * (JR.query(fb0 * lo, fb1 * hi, yb >= 0))
        ok = ub < Lam
        ncell += int(ok.sum())
        bad = ~ok
        if bad.any():
            assert rad[bad].min() > 1e-6, ('FAIL', C['box'], float(m[bad][0]), float(ub[bad][0]), Lam)
            lb, hb = lo[bad], hi[bad]; mb = (lb + hb) / 2
            lo = np.concatenate([lb, mb]); hi = np.concatenate([mb, hb])
        else:
            break
    return Lam, ncell


if __name__ == '__main__':
    certs = [c for f in sys.argv[1:] for c in json.load(open(f))]
    tmax = max(max(150.0, float(c['T'])) for c in certs)
    JR = J0Range(1.05 * tmax * 1.0 + 10)
    import time; t0 = time.time()
    for C in certs:
        check(C, JR)
    print(len(certs), f'boxes OK (fast independent check, {time.time()-t0:.1f}s)')
    A0, A1 = F(os.environ.get('A0', '13/20')), F(os.environ.get('A1', '7/10'))
    cuts = sorted({F(c['box'][0][0]) for c in certs} | {F(c['box'][0][1]) for c in certs})
    assert cuts[0] <= A0 and cuts[-1] >= A1
    for lo_, hi_ in zip(cuts, cuts[1:]):
        if hi_ <= A0 or lo_ >= A1: continue
        ivs = sorted((F(c['box'][1][0]), F(c['box'][1][1])) for c in certs if F(c['box'][0][0]) <= lo_ and F(c['box'][0][1]) >= hi_)
        reach = lo_
        for s, e in ivs:
            if s <= reach: reach = max(reach, e)
        assert ivs and ivs[0][0] <= lo_ and reach >= 1, ('coverage gap', float(lo_), float(hi_), float(reach))
    print('coverage OK: every (a,b) with', float(A0), '<= a <=', float(A1), ', a <= b <= 1')
