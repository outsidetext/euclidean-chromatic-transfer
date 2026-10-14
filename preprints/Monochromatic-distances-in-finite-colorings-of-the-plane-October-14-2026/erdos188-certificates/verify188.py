"""Independent rigorous verifier for the k>=7 certificate (Erdos #188).

Claim checked: for every delta in [0,1] there is NO pair (q, F) with
  q a probability distribution on strings s in {0,1}^w with no two adjacent 1s and no k consecutive 0s,
  E_q[s_i] = delta (all i),  E_q[s_i s_j] = F(j-i) (all i<j),
  F(r) = a0 + int_{(0,inf)} J0(t r) dnu(t),  nu >= 0,  a0 >= delta^2,  a0 + nu(0,inf) <= delta.
Each certificate (z, a, y, lam) satisfies
  (C1) z + sum_i a_i s_i + sum_{i<j} y_ij s_i s_j >= 0 for every valid s            [exact, Fractions]
  (C2) h(t) := sum_n Y_n J0(n t) <= lam for all t >= 0, Y_n = sum_{j-i=n} y_ij       [arb ball arithmetic + tail]
  (C3) q(d) := z + d*sum(a) + d^2*sum(Y) + lam*(d - d^2) < 0 on its interval         [exact]
Then E[C1] >= 0 gives 0 <= z + d sum a + a0 sum Y + lam (d - a0) <= q(d) < 0 (using sum Y = h(0) <= lam, a0 >= d^2).
usage: verify188.py certs.json"""
import sys, json, itertools
from fractions import Fraction as Fr
from flint import arb, ctx

ctx.prec = 80
certs = json.load(open(sys.argv[1]))

def valid(s, k):
    if any(s[i] and s[i+1] for i in range(len(s)-1)): return False
    run = 0
    for b in s:
        run = 0 if b else run + 1
        if run >= k: return False
    return True

def arbfr(x): return arb(x.numerator) / arb(x.denominator)

def check_C2(Y, lam):
    ns = sorted(n for n in Y if Y[n] != 0)
    Ya = {n: arbfr(Y[n]) for n in ns}
    lam_a = arbfr(lam)
    # tail: |J0(x)| <= sqrt(2/(pi x)) for x>0 (Watson 13.74: x(J0^2+Y0^2) increases to 2/pi)
    S = sum(abs(float(Y[n])) / float(n) ** 0.5 for n in ns)
    T = int((2 / 3.141592653589793) * (S / float(lam)) ** 2 * 1.02) + 2
    tail = sum((abs(Ya[n]) * (arb(2) / (arb.pi() * n * T)).sqrt() for n in ns), arb(0))
    assert tail.upper() < lam_a.lower(), "tail bound failed"
    M2 = sum((abs(Ya[n]) * n * n for n in ns), arb(0))     # |h''| <= sum |Y_n| n^2 * max|J0''|, |J0''|=|J2-J0|/2 <= 1
    # adaptive cells on [0, T]
    stack = [(Fr(0), Fr(T))]
    cells = 0
    while stack:
        lo, hi = stack.pop()
        c = (lo + hi) / 2; r = (hi - lo) / 2
        ca, ra = arbfr(c), arbfr(r)
        h = sum((Ya[n] * (ca * n).bessel_j(0) for n in ns), arb(0))
        hp = sum((Ya[n] * n * (ca * n).bessel_j(1) for n in ns), arb(0))   # |h'(c)| = |sum Y_n n J1(nc)|
        ub = h + abs(hp) * ra + M2 * ra * ra / 2
        if ub.upper() < lam_a.lower():
            cells += 1; continue
        if r < Fr(1, 10**7): raise AssertionError(f"C2 fails near t={float(c)}: h={h}")
        stack += [(lo, c), (c, hi)]
    return T, cells

covered = []
for idx, C in enumerate(certs):
    w, k = C['w'], C['k']
    z = Fr(C['z']); a = [Fr(v) for v in C['a']]; lam = Fr(C['lam'])
    y = {tuple(map(int, key.split(','))): Fr(v) for key, v in C['y'].items()}
    assert lam >= 0
    # C1
    nstr = 0
    for s in itertools.product((0, 1), repeat=w):
        if not valid(s, k): continue
        nstr += 1
        val = z + sum(a[i] for i in range(w) if s[i]) + sum(v for (i, j), v in y.items() if s[i] and s[j])
        assert val >= 0, f"C1 fails on {s}"
    Y = {}
    for (i, j), v in y.items():
        assert 0 <= i < j < w
        Y[j - i] = Y.get(j - i, Fr(0)) + v
    # C2
    T, cells = check_C2(Y, lam)
    B = sum(Y.values()); A = sum(a)
    assert B <= lam   # h(0) <= lam (also implied by C2)
    # C3 on claimed interval
    lo, hi = Fr(C['claimed'][0]), Fr(C['claimed'][1])
    q = lambda d: z + A * d + B * d * d + lam * (d - d * d)
    pts = [lo, hi]
    c2, c1 = B - lam, A + lam
    if c2 != 0:
        v = -c1 / (2 * c2)
        if lo < v < hi: pts.append(v)
    assert all(q(p) < 0 for p in pts), "C3 fails"
    covered.append((lo, hi))
    print(f"cert {idx}: w={w} k={k} strings={nstr} C1 ok; C2 ok (T={T}, {cells} cells); C3 ok on [{float(lo):.5f},{float(hi):.5f}]", flush=True)

covered.sort()
x = Fr(0)
for lo, hi in covered:
    assert lo <= x, f"gap at {float(x)}"
    x = max(x, hi)
assert x >= 1, "does not reach 1"
print("ALL CHECKS PASSED: the intervals cover [0,1]; no admissible (delta, F) exists, hence k >= 7.")
