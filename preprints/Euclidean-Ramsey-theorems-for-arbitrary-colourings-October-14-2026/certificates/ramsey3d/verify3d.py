"""Independent rigorous verifier for E^3 -> (l2, lk) certificates (pattern LP + Omega_3 Fourier bound).

Setting. Let s be an O(3)-and-translation-invariant random 0/1 field on R^3 ("red points") such that, a.s.
on every finite configuration: no two red points at distance 1, and every unit-step k-term AP has a red point.
Let delta = P(s_x = 1) and F(r) = P(s_x = s_y = 1) for |x-y| = r > 0. Then (see README / notes)
  F(r) = a0 + int_(0,inf) Om3(r t) dnu(t),  Om3(x) = sin(x)/x,  nu >= 0,  a0 >= delta^2,  a0 + nu(0,inf) <= delta,
and F(1) = 0. Such a field exists if some red/blue coloring of R^3 has no red unit pair and no blue unit-step k-AP.

Certificate (JSON): {k, cap, certs: [ {lam, Y1, claimed:[lo,hi], blocks:[{points, z, a, y, cong}]} ]}.
Points are integer triples with even coordinate sum, the real point being p/sqrt(2); squared distances are
D(p,q) = |p-q|^2/2 (integers). Blocks with "coords": "rational" instead give exact rational coordinates
(the real point is p itself, D = |p-q|^2). For each cert the verifier checks:
 (C1) for every block and EVERY valid pattern s (enumerated here from scratch):
      z + sum_i a_i s_i + sum_{ij} y_ij s_i s_j + sum_cong sum_T c_T (1[s_A = T] - 1[s_B = T]) >= 0   (exact)
      where each congruence pair (A,B) is checked to have identical ordered distance matrices, so
      E 1[s_A = T] = E 1[s_B = T] by isometry invariance.
 (C2) h(t) := Y1 Om3(t) + sum_D Y_D Om3(sqrt(D) t) <= lam for all t >= 0, Y_D = sum of y over pairs at squared
      distance D (all blocks); arb ball arithmetic on Taylor cells (|Om3''| <= 1/3) and tail |Om3(x)| <= 1/x.
 (C3) q(d) := Z + d A + d^2 h(0) + lam (d - d^2) < 0 on [lo, hi], Z = sum z, A = sum a          (exact)
Soundness: 0 <= E[C1] = Z + delta A + sum_D Y_D F(sqrt D) (+ Y1 F(1) = 0) = Z + delta A + a0 h(0) + int h dnu
           <= Z + delta A + a0 h(0) + lam (delta - a0) <= q(delta)   (h(0) <= lam, a0 >= delta^2, lam >= 0).
The intervals must cover [0, cap] (cap given) or [0, 1] (cap = null). With a cap, the conclusion additionally
uses delta <= cap, which is supplied by the m1(R^3) certificate research/m1r3/cert_final.json
(delta <= 0.14851122983... < cap = 0.1485113); see NOTES.md for why its hypotheses hold here.
usage: verify3d.py cert.json [k_expected]"""
import sys, json, itertools
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 128

FCC = True   # set per block: FCC integer coords (real point p/sqrt2) or exact rational coords (real point p)
def D(p, q):
    s = sum((x - y) ** 2 for x, y in zip(p, q))
    if FCC:
        assert s % 2 == 0
        return s // 2
    return Fr(s)

def valid_patterns(pts, k):
    n = len(pts); pos = {tuple(p): i for i, p in enumerate(pts)}
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if D(pts[i], pts[j]) == 1]
    aps = set()
    for i in range(n):
        for j in range(n):
            if i != j and D(pts[i], pts[j]) == 1:
                u = [b - a for a, b in zip(pts[i], pts[j])]   # exact (int or Fraction)
                prog = [tuple(a + m * c for a, c in zip(pts[i], u)) for m in range(k)]
                if all(q in pos for q in prog): aps.add(frozenset(pos[q] for q in prog))
    edgemask = [0] * n
    for i, j in edges: edgemask[i] |= 1 << j; edgemask[j] |= 1 << i
    apmasks = [sum(1 << x for x in ap) for ap in aps]
    # constraints are checked when their highest index is assigned
    ap_at = [[] for _ in range(n)]
    for m_ in apmasks: ap_at[m_.bit_length() - 1].append(m_)
    out = []
    def rec(i, red, blue):
        if i == n: out.append(red); return
        bit = 1 << i
        if not (edgemask[i] & red & (bit - 1)):
            rec(i + 1, red | bit, blue)
        nb = blue | bit
        if all((m_ & nb) != m_ for m_ in ap_at[i]):
            rec(i + 1, red, nb)
    rec(0, 0, 0)
    return out, len(aps), len(edges)

def arbfr(x): return arb(x.numerator) / arb(x.denominator)

def check_C2(Y, lam):
    """h(t) = sum_D Y_D Om3(sqrt(D) t) <= lam on [0, inf)."""
    Ds = sorted(d for d in Y if Y[d] != 0)
    lam_a = arbfr(lam)
    assert lam > 0
    Ya = {d: arbfr(Y[d]) for d in Ds}; sq = {d: arbfr(Fr(d)).sqrt() for d in Ds}
    S = sum((abs(Ya[d]) / sq[d] for d in Ds), arb(0))
    # tail: |h(t)| <= S / t < lam for t >= T
    T = int(float((S / lam_a).upper()) * 1.05) + 2
    assert (S / T).upper() < lam_a.lower()
    M2 = sum((abs(Ya[d]) * arbfr(Fr(d)) for d in Ds), arb(0)) / 3      # |Om3''(x)| <= 1/3  (Om3(x) = int_0^1 cos(xu) du)
    stack = [(Fr(0), Fr(T))]; cells = 0; worst = -1e9
    while stack:
        lo, hi = stack.pop()
        c = (lo + hi) / 2; r = (hi - lo) / 2
        ca, ra = arbfr(c), arbfr(r)
        h = arb(0); hp = arb(0)
        for d in Ds:
            x = ca * sq[d]; sx, cx = x.sin(), x.cos()
            h += Ya[d] * sx / x
            hp += Ya[d] * sq[d] * (x * cx - sx) / (x * x)
        ub = h + abs(hp) * ra + M2 * ra * ra / 2
        if ub.upper() < lam_a.lower():
            cells += 1; worst = max(worst, float(h.upper())); continue
        if r < Fr(1, 10 ** 9): raise AssertionError(f"C2 fails near t={float(c)}: h={h}, lam={float(lam)}")
        stack += [(lo, c), (c, hi)]
    return T, cells, worst

def main(fn, kexp=None):
    J = json.load(open(fn))
    k = J['k']
    if kexp is not None: assert k == kexp, "k mismatch"
    cap = Fr(J['cap']) if J.get('cap') else None
    if cap is not None: assert cap == Fr(1485113, 10 ** 7), "unexpected cap"
    top = cap if cap is not None else Fr(1)
    patcache = {}; covered = []
    for ci, C in enumerate(J['certs']):
        lam = Fr(C['lam']); assert lam > 0
        Y = {Fr(1): Fr(C['Y1'])}; Z = Fr(0); A = Fr(0)
        for B in C['blocks']:
            global FCC
            FCC = B.get('coords', 'fcc') == 'fcc'
            if FCC:
                pts = [tuple(int(x) for x in p) for p in B['points']]
                assert all(sum(p) % 2 == 0 for p in pts)
            else:
                assert B['coords'] == 'rational'
                pts = [tuple(Fr(x) for x in p) for p in B['points']]
            n = len(pts); assert len(set(pts)) == n
            key = (tuple(pts), k, FCC)
            if key not in patcache: patcache[key] = valid_patterns(pts, k)
            pats, naps, nedges = patcache[key]
            z = Fr(B['z']); a = [Fr(x) for x in B['a']]; assert len(a) == n
            y = {}
            for kk, val in B['y'].items():
                i, j = map(int, kk.split(',')); assert 0 <= i < j < n
                y[(i, j)] = Fr(val)
            congs = []
            for cg in B.get('cong', []):
                Ai, Bi = cg['A'], cg['B']; assert len(Ai) == len(Bi)
                assert len(set(Ai)) == len(Ai) and len(set(Bi)) == len(Bi)
                for x in range(len(Ai)):
                    for w in range(x + 1, len(Ai)):
                        assert D(pts[Ai[x]], pts[Ai[w]]) == D(pts[Bi[x]], pts[Bi[w]]), "congruence fails"
                cv = {}
                for tkey, val in cg['c'].items():
                    assert len(tkey) == len(Ai) and set(tkey) <= {'0', '1'}
                    cv[tkey] = Fr(val)
                congs.append((Ai, Bi, cv))
            # exact C1 on a common denominator
            dens = [x.denominator for x in a] + [x.denominator for x in y.values()] + [z.denominator] + \
                   [x.denominator for _, _, cv in congs for x in cv.values()]
            L = 1
            for d_ in dens: L = L * d_ // __import__('math').gcd(L, d_)
            ai = [int(x * L) for x in a]; yi = {pr: int(v * L) for pr, v in y.items()}; zi = int(z * L)
            cvi = [(Ai, Bi, {t: int(v * L) for t, v in cv.items()}) for Ai, Bi, cv in congs]
            worst = None
            for red in pats:
                val = zi
                for i in range(n):
                    if red >> i & 1: val += ai[i]
                for (i, j), v in yi.items():
                    if red >> i & 1 and red >> j & 1: val += v
                for Ai, Bi, cv in cvi:
                    ta = ''.join('1' if red >> x & 1 else '0' for x in Ai)
                    tb = ''.join('1' if red >> x & 1 else '0' for x in Bi)
                    val += cv.get(ta, 0) - cv.get(tb, 0)
                assert val >= 0, f"C1 fails on pattern {bin(red)}"
                worst = val if worst is None else min(worst, val)
            for (i, j), v in y.items():
                d = Fr(D(pts[i], pts[j])); Y[d] = Y.get(d, Fr(0)) + v
            Z += z; A += sum(a)
            print(f"  cert {ci} block: {n} pts, {nedges} unit pairs, {naps} {k}-APs, {len(pats)} valid patterns, C1 ok (min slack {worst}/{L})", flush=True)
        T, cells, hw = check_C2(Y, lam)
        h0 = sum(Y.values()); assert h0 <= lam
        lo, hi = Fr(C['claimed'][0]), Fr(C['claimed'][1]); assert 0 <= lo <= hi
        q = lambda d: Z + A * d + h0 * d * d + lam * (d - d * d)
        cand = [lo, hi]; c2, c1 = h0 - lam, A + lam
        if c2 != 0:
            v = -c1 / (2 * c2)
            if lo < v < hi: cand.append(v)
        assert all(q(p) < 0 for p in cand), "C3 fails"
        covered.append((lo, hi))
        print(f"cert {ci}: C2 ok (T={T}, {cells} cells, max h(center) ~ {hw:.6f} < lam={float(lam):.6f}); C3 ok on [{float(lo):.5f},{float(hi):.5f}]", flush=True)
    covered.sort(); x = Fr(0)
    for lo, hi in covered:
        assert lo <= x, f"gap at {float(x)}"
        x = max(x, hi)
    assert x >= top, f"coverage reaches only {float(x)} < {float(top)}"
    if cap is None:
        print(f"ALL CHECKS PASSED: no admissible delta in [0,1]. Hence E^3 -> (l2, l{k}).")
    else:
        print(f"ALL CHECKS PASSED on [0, {cap}]. With delta <= m1(R^3) <= 0.14851123 < {float(cap)} "
              f"(research/m1r3/cert_final.json, verify_cert.py), E^3 -> (l2, l{k}).")

if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else None)
