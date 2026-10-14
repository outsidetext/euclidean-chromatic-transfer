"""Independent rigorous check of two-distance Delsarte certificates
h_d(t) = 1 + a J0(t) + b J0(d t) >= 0 for all d in [d1,d2], t >= 0.

Rigor: all Bessel point values from arb (python-flint) ball arithmetic.
Interval lower bound of J0 on [m-r, m+r]:
    J0(m+u) >= J0(m) - |J1(m)| r - r^2/2      (J0' = -J1, |J0''| = |J2-J0|/2 <= 1)
Tail: |J0(x)| <= sqrt(2/(pi x)) for all x > 0 (Watson 13.74: x(J0^2+Y0^2) increases to 2/pi).
"""
import sys, time, math
import numpy as np
from flint import arb, ctx
from fractions import Fraction as F

ctx.prec = 80
S = 1.0 / 1024          # table cell width (exact binary)
XMAX = 1024.0           # table range [0, XMAX]
NC = int(XMAX / S)
PI = arb.pi()

def low_seg(p, q):
    """rigorous lower bound (float) for min J0 on [p,q], p<=q floats."""
    m = (arb(p) + arb(q)) / 2
    r = (arb(q) - arb(p)) / 2
    v = m.bessel_j(0) - abs(m.bessel_j(1)) * r - r * r / 2
    return float(v.lower())  # arb lower() returns arb; float of exact endpoint ok below

def lowf(v):
    # round arb lower endpoint down to a float safely
    lo = v.lower()
    f = float(lo)
    if arb(f) > lo:
        f = math.nextafter(f, -math.inf)
    return f

def low_seg_r(p, q):
    m = (arb(p) + arb(q)) / 2
    r = (arb(q) - arb(p)) / 2
    return lowf(m.bessel_j(0) - abs(m.bessel_j(1)) * r - r * r / 2)

def upf(v):
    hi = v.upper(); f = float(hi)
    if arb(f) < hi:
        f = math.nextafter(f, math.inf)
    return f

def build_table():
    t0 = time.time()
    tab = np.empty(NC)
    r = S / 2
    for k in range(NC):
        m = arb(k * S + r)   # exact
        tab[k] = lowf(m.bessel_j(0) - abs(m.bessel_j(1)) * r - arb(r * r / 2))
    # sparse table for range min
    sp = [tab]
    j = 1
    while (1 << j) <= NC:
        prev = sp[-1]; h = 1 << (j - 1)
        sp.append(np.minimum(prev[:-h], prev[h:]))
        j += 1
    print(f"table built: {NC} cells in {time.time()-t0:.1f}s", flush=True)
    return sp

def rmq(sp, i, j):  # min tab[i..j] inclusive
    L = j - i + 1
    k = L.bit_length() - 1
    return min(sp[k][i], sp[k][j - (1 << k) + 1])

ENV_XMAX = None

def low_J0_range(sp, x0, x1):
    """rigorous lower bound of min J0 on [x0,x1] (floats, x0<=x1, x0>=0)."""
    res = math.inf
    if x1 > XMAX:
        res = min(res, ENV_XMAX if x0 < XMAX else -upf((2 / (PI * arb(x0))).sqrt()))
        if x0 >= XMAX:
            return res
        x1 = XMAX
    if x1 - x0 <= 4 * S:
        return min(res, low_seg_r(x0, x1))
    i = math.ceil(x0 / S); j = math.floor(x1 / S)
    if i * S > x0:
        res = min(res, low_seg_r(x0, i * S))
    if j * S < x1:
        res = min(res, low_seg_r(j * S, x1))
    if j - 1 >= i:
        res = min(res, rmq(sp, i, j - 1))
    return res

def check_row(sp, d1, d2, a, b, T, step=1/128, maxdepth=14):
    """Prove h>=0 on [d1,d2] x [0,inf). Returns (ok, min lower bound, nboxes)."""
    assert b >= 0 and a >= 0
    A, B = arb(a), arb(b)
    # tail t > T
    tail = 1 - A * (2 / (PI * T)).sqrt() - B * (2 / (PI * arb(d1) * T)).sqrt()
    tail_lo = lowf(tail)
    if tail_lo <= 0:
        return False, ("tail", tail_lo), 0
    worst = (math.inf, None)
    nbox = 0
    stack = [(k * step, (k + 1) * step, 0) for k in range(int(math.ceil(T / step)))][::-1]
    while stack:
        t0, t1, dep = stack.pop()
        nbox += 1
        jt = low_seg_r(t0, t1)
        x0 = lowf(arb(d1) * arb(t0)); x1 = upf(arb(d2) * arb(t1))
        jd = low_J0_range(sp, max(x0, 0.0), x1)
        v = lowf(1 + A * arb(jt) + B * arb(jd))
        if v > 0:
            if v < worst[0]:
                worst = (v, (t0, t1))
            continue
        if dep >= maxdepth:
            return False, ("box", t0, t1, v), nbox
        tm = (t0 + t1) / 2
        stack.append((tm, t1, dep + 1)); stack.append((t0, tm, dep + 1))
    return True, (worst, tail_lo), nbox

def main():
    global ENV_XMAX
    sp = build_table()
    ENV_XMAX = -upf((2 / (PI * arb(XMAX))).sqrt())
    jobs = [
        ("~/hadwiger-nelson/multidist/cover_t7_7.0_10000.0.npy", 7.0, 10000.0, 6),
        ("~/hadwiger-nelson/multidist/cover_t7_1.77_1.92.npy", "1.77", "1.92", 6),
        ("~/hadwiger-nelson/multidist/cover_t8_16.0_10000.0.npy", 16.0, 10000.0, 7),
        ("~/hadwiger-nelson/multidist/cover_t9_40.0_10000.0.npy", 40.0, 10000.0, 8),
        ("~/hadwiger-nelson/multidist/cover_t10_150.0_10000.0.npy", 150.0, 10000.0, 9),
    ]
    import os
    for path, lo, hi, thr in jobs:
        p = os.path.expanduser(path)
        if not os.path.exists(p):
            print("MISSING", path); continue
        R = np.load(p)
        print(f"\n== {path}  rows={len(R)}  target 1+a+b>{thr}", flush=True)
        t0 = time.time()
        allok = True
        # coverage: exact rational comparison of float endpoints with decimal targets
        lo_q, hi_q = F(str(lo)), F(str(hi))
        if F(R[0, 0]) != lo_q:
            print(f"  NOTE start float {F(R[0,0])} != {lo_q} (diff {float(F(R[0,0])-lo_q):.2e}); widening first row down")
        if F(R[-1, 1]) != hi_q:
            print(f"  NOTE end float differs from {hi_q} by {float(F(R[-1,1])-hi_q):.2e}; widening last row up")
        for i in range(len(R) - 1):
            if R[i, 1] != R[i + 1, 0]:
                print(f"  GAP between rows {i},{i+1}: {R[i,1]!r} vs {R[i+1,0]!r}"); allok = False
        for i, (d1, d2, a, b) in enumerate(R):
            if i == 0 and F(d1) > lo_q:
                d1 = math.nextafter(float(lo_q), -math.inf)
            if i == len(R) - 1 and F(d2) < hi_q:
                d2 = math.nextafter(float(hi_q), math.inf)
            s = 1 + F(a) + F(b)
            sok = s > thr
            T = 400.0
            ok, info, nb = check_row(sp, float(d1), float(d2), float(a), float(b), T)
            allok &= ok and sok and b >= 0 and d1 < d2
            if ok:
                (wv, wt), tail = info
                print(f"  row {i:2d} [{d1:.6g},{d2:.6g}] a={a:.5f} b={b:.5f} 1+a+b={float(s):.5f}{'' if sok else ' FAIL-SUM'}"
                      f"  min h_lo={wv:.5f} at t~{wt[0]:.4f} tail_lo={tail:.3f} boxes={nb}", flush=True)
            else:
                print(f"  row {i:2d} FAILED: {info}", flush=True)
        print(f"  RESULT: {'VERIFIED' if allok else 'FAILED'}  ({time.time()-t0:.1f}s)", flush=True)

if __name__ == "__main__":
    main()
