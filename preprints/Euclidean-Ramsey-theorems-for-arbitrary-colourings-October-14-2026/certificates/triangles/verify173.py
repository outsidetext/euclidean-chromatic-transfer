"""Independent rigorous verifier for 2-colour monochromatic-triangle certificates (Erdos #173).

Claim certified: every red/blue colouring of R^2 contains a monochromatic congruent copy of the triangle T with
squared side lengths sides2 (rationals; T has a copy with algebraic vertices).

Soundness (see README.md): if some colouring had no monochromatic copy of T, Folner averaging over E x| K
(E = algebraic plane, K = algebraic rotations) plus colour-swap symmetrisation gives an invariant random +-1
colouring sigma of E in which a.s. no algebraic copy of T is monochromatic, and (OpenAI Thm 2.3, as in
monochromatic.tex Thm tri) E sigma(x) sigma(y) = C(|x-y|) = int_{[0,inf)} J0(|x-y| t) dG(t) for x != y,
G >= 0, G[0,inf) <= 1.  The certificate gives
  * configurations X_j (points (m,n) of the lattice Z u + Z v, |u|^2=G11, u.v=G12, |v|^2=G22) with pair
    weights y^j; L_j := min over T-free patterns s on X_j of sum y^j_ab s_a s_b   (computed here, exactly);
    T-free = no triple of X_j with squared distances sides2 is monochromatic;
  * auxiliary triangles (r1,r2,r3) (possibly degenerate) with signs sg, weights mu_k >= 0; for every +-1
    pattern sum_i sg_i s s >= -1 (checked here), so E[...] = sg.C >= -1.
Then  sum_j L_j - sum_k mu_k <= E[sum_j sum y s s + sum_k mu_k sum sg s s] = int f dG,
  f(t) = sum_r c_r J0(r t),  and int f dG <= max(0, sup f).  The verifier checks
  Lam := sum_j L_j - sum_k mu_k > 0  and  f(t) < Lam for all t >= 0   =>  contradiction.
C2 check: Arb balls on adaptive cells of [0,T] with second-order Taylor bound (|J0''| <= 1); tail t >= T via
|J0(x)| <= sqrt(2/(pi x)).
usage: verify173.py cert.json [more certs...]
"""
import sys, json, itertools
from fractions import Fraction as Fr
from flint import arb, ctx
ctx.prec = 80

def arbfr(x): return arb(x.numerator) / arb(x.denominator)

def tfree_patterns(n, triples):
    by_last = [[] for _ in range(n)]
    for tr in triples: by_last[max(tr)].append(tr)
    out = []; s = [0] * n
    s[0] = 1   # colour-swap symmetry: the energies are even, so fixing s_0 = +1 loses nothing
    def rec(i):
        if i == n: out.append(tuple(s)); return
        for v in (1, -1):
            s[i] = v
            if all(abs(s[p] + s[q] + s[r]) != 3 for (p, q, r) in by_last[i]): rec(i + 1)
        s[i] = 0
    if all(abs(s[p] + s[q] + s[r]) != 3 for (p, q, r) in by_last[0]): rec(1)
    return out

def check_f(c, Lam, T):
    """c: dict r2 (Fraction) -> coefficient (Fraction). Verify sum c J0(sqrt(r2) t) < Lam on [0, inf)."""
    keys = [k for k in c if c[k] != 0]
    ca = {k: arbfr(c[k]) for k in keys}; sq = {k: arbfr(k).sqrt() for k in keys}
    lam = arbfr(Lam); Ta = arb(T)
    tail = sum((abs(ca[k]) * (arb(2) / (arb.pi() * sq[k] * Ta)).sqrt() for k in keys), arb(0))
    assert tail.upper() < lam.lower(), f"tail bound {tail} not below Lam={float(Lam)} at T={T}"
    M2 = sum((abs(ca[k]) * arbfr(k) for k in keys), arb(0))
    stack = [(Fr(0), Fr(T))]; cells = 0; worst = -1e9
    while stack:
        lo, hi = stack.pop(); cc = (lo + hi) / 2; rr = (hi - lo) / 2
        x, rad = arbfr(cc), arbfr(rr)
        h = arb(0); hp = arb(0)
        for k in keys:
            z = x * sq[k]
            h += ca[k] * z.bessel_j(0); hp += ca[k] * sq[k] * z.bessel_j(1)   # f' = -sum c r J1
        ub = h + abs(hp) * rad + M2 * rad * rad / 2
        if ub.upper() < lam.lower():
            cells += 1; worst = max(worst, float(h.mid())); continue
        if rr < Fr(1, 10**7): raise AssertionError(f"C2 fails near t={float(cc)}: f={h}, Lam={float(Lam)}")
        stack += [(lo, cc), (cc, hi)]
    return cells, worst, float(tail.upper())

def verify(path):
    C = json.load(open(path))
    s2 = sorted(Fr(x) for x in C['sides2']); assert all(x > 0 for x in s2)
    a2, b2, c2 = s2
    # triangle inequality (non-strict: degenerate allowed) for sqrt sides: (a+b)^2 >= c^2 <=> 2ab >= c2-a2-b2
    rhs = c2 - a2 - b2; assert rhs <= 0 or 4 * a2 * b2 >= rhs * rhs, "sides2 not a triangle"
    G11, G12, G22 = (Fr(x) for x in C['gram'])
    assert G11 > 0 and G11 * G22 - G12 * G12 > 0
    q = lambda d: G11 * d[0] * d[0] + 2 * G12 * d[0] * d[1] + G22 * d[1] * d[1]
    coef = {}; Ltot = Fr(0)
    for j, X in enumerate(C['configs']):
        P = [tuple(p) for p in X['points']]; n = len(P); assert len(set(P)) == n
        D = {(i, k): q((P[i][0] - P[k][0], P[i][1] - P[k][1])) for i in range(n) for k in range(i + 1, n)}
        triples = [(i, k, l) for i, k, l in itertools.combinations(range(n), 3)
                   if sorted([D[(i, k)], D[(i, l)], D[(k, l)]]) == s2]
        y = {}
        for key, val in X['y'].items():
            i, k = map(int, key.split(',')); assert 0 <= i < k < n; y[(i, k)] = Fr(val)
        pats = tfree_patterns(n, triples)
        assert pats, "no T-free pattern on a configuration (then T is trivially forced; handle separately)"
        Lj = min(sum(v * s[i] * s[k] for (i, k), v in y.items()) for s in pats)
        for (i, k), v in y.items(): coef[D[(i, k)]] = coef.get(D[(i, k)], Fr(0)) + v
        Ltot += Lj
        print(f"  config {j}: {n} points, {len(triples)} copies of T, {len(pats)} T-free patterns (s_0=+1), L_{j} = {float(Lj):.6f}")
    mutot = Fr(0)
    allpat = list(itertools.product((1, -1), repeat=3))
    for A in C['aux']:
        r = [Fr(x) for x in A['r']]; sg = tuple(A['sg']); mu = Fr(A['mu'])
        assert all(x > 0 for x in r) and mu >= 0 and all(z in (1, -1) for z in sg)
        assert r[0] <= r[1] + r[2] and r[1] <= r[0] + r[2] and r[2] <= r[0] + r[1], "aux not a triangle"
        # pair order: r[0] = |x1 x2|, r[1] = |x1 x3|, r[2] = |x2 x3|
        assert min(sg[0] * s[0] * s[1] + sg[1] * s[0] * s[2] + sg[2] * s[1] * s[2] for s in allpat) >= -1
        for x, z in zip(r, sg): coef[x * x] = coef.get(x * x, Fr(0)) + mu * z
        mutot += mu
    Lam = Ltot - mutot
    print(f"  sum L = {float(Ltot):.6f}, sum mu = {float(mutot):.6f}, Lam = {float(Lam):.6f}, {len(coef)} distinct distances")
    assert Lam > 0
    cells, worst, tail = check_f(coef, Lam, C['T'])
    print(f"  C2 ok: f < Lam on [0,{C['T']}] ({cells} cells, max centre value {worst:.5f}); tail bound {tail:.5f} < Lam")
    print(f"CERTIFIED: every 2-colouring of the plane has a monochromatic triangle with squared sides {[str(x) for x in s2]}")

if __name__ == "__main__":
    for p in sys.argv[1:]:
        print(p); verify(p)
