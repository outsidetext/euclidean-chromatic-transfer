"""e_k / v_k bounds from a certified upper bound p_hi on p_{k-1} (de Grey--Parts 2303.14714).
e_k >= ceil(1/p_hi)  (strictly: e*p >= 1, so e >= 1/p >= 1/p_hi)
v_k >= min{ v : maxE(v) >= e_k }, maxE from Agoston--Palvolgyi (arXiv 2006.06285):
  v<=15 exact, 16..19 upper bounds, 20<=v<521:
  largest e with  v >= 2r - 11 + 24/v + (1-s) C(floor r,2) + s C(ceil r,2),  r=2e/v, s=r-floor r
  (beyond: e <= (29/4)^(1/3) v^(4/3))."""
import math
from fractions import Fraction as Fr
SMALL = [0, 0, 1, 3, 5, 7, 9, 12, 14, 18, 20, 23, 27, 30, 33, 37, 42, 47, 52, 57]  # index v
def C2(n): return Fr(n * (n - 1), 2)
def ok(v, e):
    r = Fr(2 * e, v); fl = math.floor(r); ce = math.ceil(r); s = r - fl
    return Fr(v) >= 2 * r - 11 + Fr(24, v) + (1 - s) * C2(fl) + s * C2(ce)
def maxE(v):
    if v < len(SMALL): return SMALL[v]
    if v < 521:
        e = 0
        while ok(v, e + 1): e += 1
        return e
    return math.floor((29 / 4) ** (1 / 3) * v ** (4 / 3))
def e_from_p(p_hi):
    return math.ceil(Fr(1) / Fr(p_hi)) if not isinstance(p_hi, Fr) else math.ceil(1 / p_hi)
def v_from_e(e):
    v = 1
    while maxE(v) < e: v += 1
    return v
if __name__ == '__main__':
    print([maxE(v) for v in range(20, 60)])
    for e in (98, 99, 103, 180, 182, 186): print(e, v_from_e(e))
