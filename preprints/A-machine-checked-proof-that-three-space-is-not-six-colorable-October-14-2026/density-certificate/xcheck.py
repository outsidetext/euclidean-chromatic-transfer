"""Independent check of m1(R^3) certificate (written from scratch).

Inequality used per cut c: for all 0/1 vectors X,  sum_{p=(i,j), i<=j} z_p X_i X_j >= beta_c.
Taking expectation over random rigid motion: sum_p z_p delta g(d_p) >= beta_c (g(0)=1).
Dual: G(t) = -nu*Om(t) + sum_c y_c sum_p z_p Om(t d_p).  Need y>=0, G(0)+1 <= mu, G(t) <= mu (t>0).
Then delta <= (mu + sqrt(mu^2 - 4 sum y beta))/2.
"""
import json, sys, time, os
from fractions import Fraction as Fr
import multiprocessing as mpc
from flint import arb, ctx

ctx.prec = 128
T0 = time.time()
J = json.load(open(sys.argv[1]))
hx = lambda s: Fr(float.fromhex(s))
nu, mu = hx(J["nu"]), hx(J["mu"])
if os.environ.get("MU_OVERRIDE"): mu = Fr(os.environ["MU_OVERRIDE"]); print("NEGATIVE CONTROL mu =", float(mu))

def A(fr):  # exact rational -> arb
    return arb(fr.numerator) / arb(fr.denominator)

terms = {}            # exact squared distance -> exact coefficient (q=0 => constant)
terms[Fr(1)] = -nu
sum_yb = Fr(0); min_unit_gap = None; min_q = None; report = []
for ci, c in enumerate(J["cuts"]):
    P = [[hx(v) for v in p] for p in c["points"]]
    N = len(P)
    pairs = [(i, i) for i in range(N)] + [(i, j) for i in range(N) for j in range(i + 1, N)]
    z = [hx(v) for v in c["z"]]
    y = hx(c["y"])
    assert len(z) == len(pairs), ci
    assert y >= 0, ci
    # exact beta = min over all 2^N 0/1 vectors (no unit-distance edges assumed)
    beta = min(sum((zp for (i, j), zp in zip(pairs, z) if (m >> i) & 1 and (m >> j) & 1), Fr(0))
               for m in range(1 << N))
    sum_yb += y * beta
    nz = []
    for (i, j), zp in zip(pairs, z):
        q = sum(((P[i][k] - P[j][k]) ** 2 for k in range(3)), Fr(0))
        if i != j:
            gap = abs(q - 1)
            if min_unit_gap is None or gap < min_unit_gap: min_unit_gap = gap
            if q > 0 and (min_q is None or q < min_q): min_q = q
        if zp != 0:
            nz.append((i, j, float(zp), float(q) ** 0.5))
        terms[q] = terms.get(q, Fr(0)) + y * zp
    report.append((ci, N, float(y), float(beta), nz))

print(f"cuts={len(J['cuts'])}  sum y*beta = {sum_yb}  (exact)")
for ci, N, y, b, nz in report:
    print(f"  cut {ci:2d} N={N:2d} y={y:.4e} beta={b} nonzero z: " +
          ", ".join(f"({i},{j}):{zp:+.4g}@d={d:.6f}" for i, j, zp, d in nz))
print(f"min |d^2-1| over all pairs = {float(min_unit_gap):.3e};  min nonzero d = {float(min_q)**0.5:.3e}")
w0 = terms.pop(Fr(0), Fr(0))
qs = sorted(q for q in terms if terms[q] != 0)
G0 = w0 + sum(terms[q] for q in qs)
print(f"w0 = {float(w0):.12f}, G(0) = {float(G0):.12f}, mu = {float(mu):.15f}")
cond_i = (G0 + 1 <= mu)
print(f"(i) exact: mu - G(0) - 1 = {float(mu - G0 - 1):.6e}  -> {'OK' if cond_i else 'FAIL'}")
assert cond_i

S = [arb(q.numerator).sqrt() / arb(q.denominator).sqrt() for q in qs]
W = [A(terms[q]) for q in qs]
W0, MU = A(w0), A(mu)
Sf = [float(q) ** 0.5 for q in qs]; Wf = [float(terms[q]) for q in qs]
print(f"distinct nonzero distances in G: {len(qs)}")

# ---- small t: |Om(x)-1| <= x^2/6, so G(t) <= G(0) + t^2 sum|w| s^2 / 6
M2 = sum(abs(A(terms[q])) * A(q) for q in qs)
t0 = 0.5
small = A(G0) + arb(t0) ** 2 * M2 / 6
assert small < MU, small
print(f"(0,{t0}]: G <= {small.str(8)} < mu")

# ---- tail t >= L: |Om(x)| <= 1/x
Wsum = sum(abs(w) / s for w, s in zip(W, S))
kappa = MU - W0
L = float((Wsum / (kappa * 0.5)).upper()) + 1
tailb = W0 + Wsum / arb(L)
assert tailb < MU
print(f"[L={L:.2f}, inf): G <= {tailb.str(8)} < mu")

ONE3 = arb(0, arb(1) / 3)  # ball [-1/3, 1/3]

def om012(x):
    s, c = x.sin_cos()
    om = s / x
    om1 = (x * c - s) / (x * x)
    return om, om1

def om2_ball(x):
    # |Om''| <= 1/3 always (Om(x)=int_0^1 cos(ux)du); use closed form when x is away from 0
    if x.lower() > 2:
        s, c = x.sin_cos()
        v = -s / x - 2 * c / (x * x) + 2 * s / (x * x * x)
        return v
    return ONE3

def check_cell(a, b):
    """True if G(t) < mu on [a,b] proven by 2nd order Taylor: G(c)+G'(c)v+G''(ball)v^2/2."""
    c = (a + b) / 2; r = max(c - a, b - c) * (1 + 1e-12)
    ca = arb(c); ball = arb(c, r)
    g = W0; g1 = arb(0); g2 = arb(0)
    for s, w in zip(S, W):
        om, om1 = om012(ca * s)
        g += w * om; g1 += w * s * om1
        g2 += w * s * s * om2_ball(ball * s)
    ra = arb(r)
    # Taylor/Lagrange: G(c+v) <= G(c) + G'(c) v + M v^2/2,  M = upper bound of G'' on the cell.
    a = arb(abs(g1).upper()); M = arb(g2.upper())
    if M >= 0 or not (M < 0):
        M = arb(max(float(M.upper()), 0.0)) if not (M < 0) else M
    if M < 0:
        Mabs = -M
        if (a - Mabs * ra) > 0:          # vertex outside the cell: max at |v| = r
            inc = a * ra + M * ra * ra / 2
        else:                            # global max of the concave quadratic (always valid)
            inc = a * a / (2 * Mabs)
    else:
        inc = a * ra + M * ra * ra / 2
    up = arb((g + inc).upper())
    return up < MU, float(up.upper())

def run_range(args):
    lo, hi = args
    stack = [(lo, hi)]; n = 0; worst = (-1, None)
    while stack:
        a, b = stack.pop()
        ok, u = check_cell(a, b)
        n += 1
        if ok:
            if u > worst[0]: worst = (u, (a + b) / 2)
        else:
            if b - a < 1e-9:
                return (lo, hi, n, worst, (a, b, u))
            m = (a + b) / 2
            stack.append((m, b)); stack.append((a, m))
    return (lo, hi, n, worst, None)

if __name__ == "__main__":
    os.nice(10)
    step = 0.02
    chunks = []
    t = t0
    while t < L:
        chunks.append((t, min(t + 2.0, L))); t += 2.0
    # inside each chunk start with width-step cells
    def expand(ch):
        lo, hi = ch
        return lo, hi
    tasks = []
    for lo, hi in chunks:
        tasks.append((lo, hi))
    # split initial cells inside run_range by bisection from 2.0 width; fine
    if len(sys.argv) > 2: tasks = [x for x in tasks if x[0] < float(sys.argv[2])]
    with mpc.get_context('fork').Pool(4) as pool:
        res = pool.map(run_range, tasks, chunksize=4)
    total = sum(r[2] for r in res)
    fails = [r for r in res if r[4] is not None]
    worst = max((r[3] for r in res if r[3][1] is not None), key=lambda x: x[0])
    print(f"[{t0}, {L:.2f}]: {total} cell evaluations, worst certified upper bound {worst[0]:.12f} at t~{worst[1]:.4f}")
    if fails:
        print("FAIL cells:", fails[:5]); sys.exit(1)
    print(f"mu - worst = {float(mu) - worst[0]:.3e}")
    sb = A(sum_yb)
    dcert = (MU + (MU * MU - 4 * sb).sqrt()) / 2
    print(f"CERTIFIED m1(R^3) <= {dcert.str(15)}  upper {float(dcert.upper())!r}")
    print(f"runtime {time.time() - T0:.1f}s")
