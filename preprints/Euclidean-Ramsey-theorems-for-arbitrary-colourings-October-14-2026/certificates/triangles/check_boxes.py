# Independent check of Erdos #173 box certificates (different method from verify_box.py):
# Lipschitz enclosures with |J0'| = |J1| <= 0.5819 (max |J1| = 0.58187...), J0 values by mpmath at 40 digits,
# J0 range on an x-interval from a cached fine grid; tail by |J0(x)| <= sqrt(2/(pi x)). Plus coverage check.
import sys, json, itertools, math
from fractions import Fraction as F
import mpmath as mp
mp.mp.dps = 40
L1 = 0.5819  # >= max|J1|
def j0(x): return float(mp.besselj(0, x))
GRID = 0.002; NG = int(200 / GRID) + 2
J = [j0(i * GRID) for i in range(NG)]
def j0_ub(lo, hi):  # upper bound of J0 on [lo,hi]
    i0, i1 = int(lo / GRID), int(math.ceil(hi / GRID))
    if i1 >= NG: return min(1.0, math.sqrt(2 / (math.pi * lo)) if lo > 0 else 1.0)
    return max(J[i0:i1 + 1]) + L1 * GRID / 2 + 1e-12
def j0_lb(lo, hi):
    i0, i1 = int(lo / GRID), int(math.ceil(hi / GRID))
    if i1 >= NG: return -math.sqrt(2 / (math.pi * lo))
    return min(J[i0:i1 + 1]) - L1 * GRID / 2 - 1e-12
def check(C):
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
    ks = [(float(k), float(c)) for k, c in fixed.items() if c != 0]
    T = 150.0
    tail = sum(abs(c) * math.sqrt(2 / (math.pi * k * T)) for k, c in ks) + abs(float(y[0])) * math.sqrt(2 / (math.pi * float(a0) * T)) + abs(float(y[1])) * math.sqrt(2 / (math.pi * float(b0) * T))
    assert tail < Lam - 1e-9, ('tail', tail, Lam)
    Lip = sum(abs(c) * k for k, c in ks) * L1
    ya, yb = float(y[0]), float(y[1]); fa0, fa1, fb0, fb1 = map(float, (a0, a1, b0, b1))
    stack = [(0.0, T)]; worst = -9
    while stack:
        lo, hi = stack.pop(); m = (lo + hi) / 2; rad = (hi - lo) / 2
        ub = sum(c * float(mp.besselj(0, k * m)) for k, c in ks) + Lip * rad + 1e-12
        ub += ya * (j0_ub(fa0 * lo, fa1 * hi) if ya >= 0 else j0_lb(fa0 * lo, fa1 * hi))
        ub += yb * (j0_ub(fb0 * lo, fb1 * hi) if yb >= 0 else j0_lb(fb0 * lo, fb1 * hi))
        if ub < Lam: worst = max(worst, ub); continue
        assert rad > 1e-5, ('FAIL', C['box'], m, ub, Lam)
        stack += [(lo, m), (m, hi)]
    return Lam, worst
certs = [c for f in sys.argv[1:] for c in json.load(open(f))]
for i, C in enumerate(certs):
    Lam, w = check(C)
print(len(certs), 'boxes OK (independent Lipschitz check)')
# coverage: union of boxes must contain {(a,b): a in [A0,A1], a <= b <= 1}
A0, A1 = F(13, 20), F(7, 10)
cuts = sorted({F(c['box'][0][0]) for c in certs} | {F(c['box'][0][1]) for c in certs})
assert cuts[0] <= A0 and cuts[-1] >= A1
for lo, hi in zip(cuts, cuts[1:]):
    if hi <= A0 or lo >= A1: continue
    ivs = sorted((F(c['box'][1][0]), F(c['box'][1][1])) for c in certs if F(c['box'][0][0]) <= lo and F(c['box'][0][1]) >= hi)
    need, reach = lo, lo  # b from a (>= lo) up to 1
    for s, e in ivs:
        if s <= reach: reach = max(reach, e)
    ok = ivs and ivs[0][0] <= lo and reach >= 1
    assert ok, ('coverage gap in a-strip', float(lo), float(hi), [(float(s), float(e)) for s, e in ivs][:3], float(reach))
print('coverage OK: every (a,b) with', float(A0), '<= a <=', float(A1), ', a <= b <= 1')
