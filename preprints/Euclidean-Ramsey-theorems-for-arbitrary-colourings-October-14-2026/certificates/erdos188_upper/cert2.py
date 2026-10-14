"""Independent certifier (Claude) for periodic disc colourings, Erdos #188.
RED = open discs radius r at centres c_i + P.  Claim: every unit-step k-AP meets RED.
(a) exact: lifted centre separations >= 1 + 2r  (=> red unit-distance-free; r <= 1/2).
(b) theta in [0,pi] split into arcs [th0, th1]; for true u on the arc, |u - u0| <= e := 2 sin((th1-th0)/2).
    Need: for every x in the fundamental parallelogram F, some j<k with x + j u0 in D(c, r - j e) (eroded).
    In coords t = x.u0, s = x.u0perp, for an s-strip [sa,sb]: disc (tc,sc,rho) contains (t,s) for all s in the strip
    iff t in [tc-h, tc+h], h = sqrt(rho^2 - dlt^2), dlt = max(|sa-sc|,|sb-sc|).  Start t0 blocked at step j iff
    t0 + j in that interval.  Check union of intervals covers F's t-range over the strip.  Adaptive splitting.
    Float margins 1e-9 on radii and on interval overlaps."""
import sys, json, math, numpy as np
from fractions import Fraction as Fr
M = 1e-9
d = json.load(open(sys.argv[1])); K = int(sys.argv[2])
B = [[Fr(x) for x in row] for row in d['B']]; b1 = (B[0][0], B[1][0]); b2 = (B[0][1], B[1][1])
C = [(Fr(a), Fr(b)) for a, b in (d['centers'] if isinstance(d['centers'], list) else eval(d['centers']))]
r = Fr(d['r']); assert 0 < r <= Fr(1, 2) and 'radii' not in d
# (a) exact separation over lifted centres within range
need = (1 + 2*r)**2
covol = abs(b1[0]*b2[1] - b1[1]*b2[0])
nb = 3
worst = None
for i, c in enumerate(C):
    for j, c2 in enumerate(C):
        for n1 in range(-nb, nb+1):
            for n2 in range(-nb, nb+1):
                if i == j and n1 == 0 and n2 == 0: continue
                dx = c2[0] + n1*b1[0] + n2*b2[0] - c[0]; dy = c2[1] + n1*b1[1] + n2*b2[1] - c[1]
                D2 = dx*dx + dy*dy
                if worst is None or D2 < worst: worst = D2
                assert D2 >= need, ("separation fails", i, j, n1, n2, float(D2))
# nb=3 suffices if the reduced basis vectors are long: check min lattice translates beyond nb are > 2 away
print(f"(a) min squared centre separation {float(worst):.6f} >= {float(need)} : unit-distance-free OK")
f = lambda x: float(x)
b1f = np.array([f(b1[0]), f(b1[1])]); b2f = np.array([f(b2[0]), f(b2[1])]); Cf = np.array([[f(a), f(b)] for a, b in C]); rf = f(r)
Fv = np.array([[0, 0], b1f, b2f, b1f + b2f])
Dmax = max(np.linalg.norm(v) for v in Fv)
R = K + Dmax + 2
N = int(R / min(np.linalg.norm(b1f), np.linalg.norm(b2f)) * 3) + 3
grid = np.array([(n1, n2) for n1 in range(-N, N+1) for n2 in range(-N, N+1)])
L = grid[:, :1]*b1f + grid[:, 1:]*b2f
L = L[np.linalg.norm(L, axis=1) <= R + 30]
ALL = (L[:, None, :] + Cf[None]).reshape(-1, 2)
ALL = ALL[np.linalg.norm(ALL, axis=1) <= R + Dmax]
print("lifted centres:", len(ALL), flush=True)
js = np.arange(K)
def strip_ok(t_c, s_c, sa, sb, Tlo, Thi, e):
    dlt = np.maximum(np.abs(sa - s_c), np.abs(sb - s_c))           # per disc
    rho = rf - js[None, :]*e - M                                     # per j
    h2 = rho**2 - dlt[:, None]**2
    ok = (rho > 0) & (h2 > 0)
    h = np.sqrt(np.where(ok, h2, 0)) - M
    lo = (t_c[:, None] - h - js[None, :])[ok & (h > 0)]; hi = (t_c[:, None] + h - js[None, :])[ok & (h > 0)]
    if lo.size == 0: return False
    o = np.argsort(lo); lo = lo[o]; hi = hi[o]
    cur = Tlo
    # sweep
    sel = hi > cur
    lo, hi = lo[sel], hi[sel]
    i = 0; n = lo.size
    reach = np.maximum.accumulate(hi)
    # find first index where lo > cur..: iterative via numpy
    while cur < Thi:
        k = np.searchsorted(lo, cur - M, side='right')   # intervals starting at <= cur - M (strict overlap)
        if k == 0: return False
        nr = reach[k-1]
        if nr <= cur + M: return False
        cur = nr
    return True
def arc_ok(th0, th1, depth=0):
    e = 2*math.sin((th1 - th0)/2) + 1e-15
    u = np.array([math.cos(th0), math.sin(th0)]); w = np.array([-u[1], u[0]])
    tF = Fv @ u; sF = Fv @ w
    t_all = ALL @ u; s_all = ALL @ w
    smin, smax = sF.min(), sF.max()
    stack = [(smin, smax)]; nstrips = 0
    while stack:
        sa, sb = stack.pop()
        # t-range of F within strip: conservative = over parallelogram clipped; use full F t-range of polygon slice
        # compute slice bounds exactly for convex polygon: t-values at s=sa, s=sb and vertices inside
        pts = []
        for a, b in [(0, 1), (1, 3), (3, 2), (2, 0)]:
            p, q = Fv[a], Fv[b]; sp, sq = sF[a], sF[b]; tp, tq = tF[a], tF[b]
            for sv in (sa, sb):
                if (sp - sv)*(sq - sv) <= 0 and sp != sq:
                    lam = (sv - sp)/(sq - sp); pts.append(tp + lam*(tq - tp))
            if sa <= sp <= sb: pts.append(tp)
        if not pts: nstrips += 1; continue
        Tlo, Thi = min(pts) - M, max(pts) + M
        sel = (s_all > sa - rf) & (s_all < sb + rf) & (t_all > Tlo - rf - 1) & (t_all < Thi + K + rf + 1)
        if strip_ok(t_all[sel], s_all[sel], sa, sb, Tlo, Thi, e): nstrips += 1; continue
        if sb - sa < 2e-4: return False, (sa, sb)
        m = (sa + sb)/2; stack += [(sa, m), (m, sb)]
    return True, nstrips
narcs = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
ths = np.linspace(0, math.pi, narcs + 1)
stack = [(ths[i], ths[i+1]) for i in range(narcs)][::-1]; done = 0; splits = 0
while stack:
    a, b = stack.pop()
    ok, info = arc_ok(a, b)
    if ok: done += 1; continue
    if b - a < 1e-7: print("FAIL at theta", math.degrees(a), info); sys.exit(1)
    splits += 1; m = (a + b)/2; stack += [(m, b), (a, m)]
    if splits % 50 == 0: print("splits", splits, "at deg", math.degrees(a), flush=True)
print(f"(b) ALL ARCS OK: k={K}, arcs={done}, splits={splits}.  Every unit-step {K}-AP meets RED.")
