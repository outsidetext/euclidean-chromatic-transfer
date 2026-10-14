"""Exact symbolic certification of the two 12-point chain configurations
(chain A: r=sqrt2, chain B: r=1+sqrt3) behind the chi>=7 argument.

Method: all coordinates live in an explicit tower of quadratic extensions.
  Chain A: K_A = Q(w2,w3,w7,S), w2^2=2, w3^2=3, w7^2=7, S^2=9+4*w3
  Chain B: K_B = Q(w3,w7,T),           w3^2=3, w7^2=7, T^2=9-4*w3
Elements are polynomials in the generators; zero-testing is by normal form
modulo the defining relations.  With generator order (S|T, w2, w7, w3) and lex
order, the relation set has pairwise-coprime leading monomials (pure squares),
hence is a Groebner basis, so normal forms are unique and the quotient ring
has dimension 16 (A) resp. 8 (B).  We certify separately (via the minimal
polynomial of a primitive element) that the field generated really has that
degree; then the quotient ring IS the field and normal-form-zero <=> zero.
So every equality/inequality decision below is exact and unconditional.
"""
import json, itertools, os, sys
import sympy as sp
from sympy import Rational as Ra, sqrt, expand

HN = os.path.dirname(os.path.abspath(__file__))

w2, w3, w7, S, T = sp.symbols('w2 w3 w7 S T', positive=True)

def make_normalizer(rels, gens):
    def nf(e):
        e = sp.expand(e)
        _, r = sp.reduced(e, rels, gens, order='lex')
        return sp.expand(r)
    return nf

def run_chain(name, fname, gens, rels, numsubs, r, cos1, sin1, cosd, sind,
              long_target, prim_elt, expect_deg):
    print('=' * 78)
    print(f'CHAIN {name}  (r = {sp.sstr(r)}, r^2 = ?)')
    nf = make_normalizer(rels, gens)
    d2 = 2 + w3                      # d^2 = 2 + sqrt3 exactly
    r2 = nf(r * r)
    print(f'  exact r^2 = {sp.sstr(r2)},  d^2 = 2 + sqrt(3)')
    results = {}

    # ---- degree certification of the tower --------------------------------
    mp = sp.minimal_polynomial(prim_elt, sp.Symbol('x'))
    deg = sp.degree(mp)
    ok = (deg == expect_deg)
    results['field degree certificate'] = ok
    print(f'  [field] minpoly degree of primitive element = {deg} '
          f'(expected {expect_deg}) -> {"PASS" if ok else "FAIL"}')
    if not ok:
        print('  FATAL: tower smaller than assumed; normal-form nonzero would '
              'not certify nonzero.'); sys.exit(1)

    # ---- trig sanity: cos^2+sin^2 = 1 for phi1, phid ----------------------
    assert nf(cos1**2 + sin1**2 - 1) == 0, 'phi1 pythagoras fails'
    assert nf(cosd**2 + sind**2 - 1) == 0, 'phid pythagoras fails'

    # ---- headings by angle addition ---------------------------------------
    cosA = nf(cosd*cos1 + sind*sin1);  sinA = nf(sind*cos1 - cosd*sin1)
    cosB = nf(cosd*cos1 - sind*sin1);  sinB = nf(sind*cos1 + cosd*sin1)
    cosAB = nf(cosA*cosB - sinA*sinB); sinAB = nf(sinA*cosB + cosA*sinB)
    cosH = [sp.Integer(1), nf(-cosA), cosAB,     nf(-cosB)]
    sinH = [sp.Integer(0), sinA,      nf(-sinAB), sinB]
    for k in range(4):
        assert nf(cosH[k]**2 + sinH[k]**2 - 1) == 0, f'heading {k} not unit'

    # ---- chain points -----------------------------------------------------
    X = [(sp.Integer(0), sp.Integer(0))]
    for i in range(6):
        k = i % 4
        X.append((nf(X[-1][0] + r*cosH[k]), nf(X[-1][1] + r*sinH[k])))

    # ---- apexes: C_i = X_i + cos(phi1)*(X_{i-1}-X_i) +/- sin(phi1)*perp ---
    fl = json.load(open(f'{HN}/{fname}'))
    FP = fl['points']; fslots = [tuple(s) for s in fl['slots']]
    def num(e):
        return float(sp.expand(e).subs(numsubs).evalf(40))
    C = []
    for i in range(1, 6):
        P, Qp = X[i], X[i-1]
        vx, vy = nf(Qp[0]-P[0]), nf(Qp[1]-P[1])
        cands = []
        for sg in (1, -1):
            cands.append((nf(P[0] + cos1*vx + sg*sin1*vy),
                          nf(P[1] + cos1*vy - sg*sin1*vx)))
        fx, fy = FP[6+i]
        match = [c for c in cands
                 if abs(num(c[0])-fx) < 1e-6 and abs(num(c[1])-fy) < 1e-6]
        assert len(match) == 1, f'apex {i}: branch ambiguous/missing'
        C.append(match[0])
    Pts = X + C
    assert len(Pts) == 12

    # ---- numeric consistency with the float file --------------------------
    md = max(max(abs(num(p[0])-q[0]), abs(num(p[1])-q[1]))
             for p, q in zip(Pts, FP))
    results['coords match float file'] = md < 1e-9
    print(f'  [coords] max |exact - float| over 24 coordinates = {md:.2e} '
          f'-> {"PASS" if md < 1e-9 else "FAIL"}')

    # ---- exact squared distances for all 66 pairs -------------------------
    q = {}
    for a, b in itertools.combinations(range(12), 2):
        dx = Pts[a][0]-Pts[b][0]; dy = Pts[a][1]-Pts[b][1]
        q[(a, b)] = nf(dx*dx + dy*dy)

    # (1) chain steps
    ok = all(q[(i, i+1)] - r2 == 0 for i in range(6))
    results['1. chain steps |X_i X_{i+1}|^2 = r^2'] = ok
    print(f'  [1] all 6 chain steps: |X_i X_(i+1)|^2 == {sp.sstr(r2)} exactly '
          f'-> {"PASS" if ok else "FAIL"}')

    # (2) apex slot distances
    ok_r = all(nf(q[tuple(sorted((i, 6+i)))] - r2) == 0 for i in range(1, 6))
    ok_1 = all(nf(q[tuple(sorted((i-1, 6+i)))] - 1) == 0 for i in range(1, 6))
    ok_d = all(nf(q[tuple(sorted((i+1, 6+i)))] - d2) == 0 for i in range(1, 6))
    results['2. apex distances (r,1,d)'] = ok_r and ok_1 and ok_d
    print(f'  [2] apexes: |C_i X_i|^2 == r^2: {"PASS" if ok_r else "FAIL"}, '
          f'|C_i X_(i-1)|^2 == 1: {"PASS" if ok_1 else "FAIL"}, '
          f'|C_i X_(i+1)|^2 == d^2 = 2+sqrt3: {"PASS" if ok_d else "FAIL"}')

    # (3) long pairs; identity |X_{i+4}-X_i| = (d^2-1)/r
    ident = nf(sp.expand((d2-1)**2) )   # (d^2-1)^2
    long_ok = True
    for (a, b) in ((0, 4), (1, 5), (2, 6)):
        z = nf(q[(a, b)] - long_target)
        zi = nf(q[(a, b)]*r2 - ident)      # q == (d^2-1)^2 / r^2
        if z != 0 or zi != 0:
            long_ok = False
            print(f'      long pair ({a},{b}): residual {sp.sstr(z)}')
    results['3. long pairs'] = long_ok
    print(f'  [3] |X0X4|^2 = |X1X5|^2 = |X2X6|^2 == {sp.sstr(long_target)} '
          f'and == (d^2-1)^2/r^2 exactly -> {"PASS" if long_ok else "FAIL"}')
    print(f'      identity value: (d^2-1)/r = (1+sqrt3)/({sp.sstr(r)}), '
          f'squared = {sp.sstr(nf(sp.cancel(ident/1)))}/{sp.sstr(r2)}')

    # (4) complete classification of all 66 pairs
    edges, nonedges, unresolved = [], [], []
    for pr, qq in q.items():
        z1 = nf(qq - 1); zd = nf(qq - d2)
        if z1 == 0 and zd == 0:
            unresolved.append(pr)          # impossible
        elif z1 == 0:
            edges.append((pr, 1))
        elif zd == 0:
            edges.append((pr, 'd'))
        else:
            nonedges.append(pr)
    assert not unresolved
    E = sorted(pr for pr, _ in edges)
    # float edges for comparison
    import math
    Dnum = (math.sqrt(6)+math.sqrt(2))/2
    Ef = sorted((a, b) for a, b in itertools.combinations(range(12), 2)
                if abs(math.dist(FP[a], FP[b])-1) < 1e-9
                or abs(math.dist(FP[a], FP[b])-Dnum) < 1e-9)
    slots_ok = all(tuple(sorted(s)) not in E for s in fslots)
    slot_r_ok = all(nf(q[tuple(sorted(s))] - r2) == 0 for s in fslots)
    ok4 = (E == Ef) and len(E) == 14 and slots_ok and slot_r_ok
    results['4. complete edge set'] = ok4
    print(f'  [4] all 66 pairs resolved exactly; edges: {len(E)} '
          f'(float file: {len(Ef)}), sets {"identical" if E==Ef else "DIFFER"}; '
          f'all 11 slots at exactly r^2 and non-edges: '
          f'{"yes" if slots_ok and slot_r_ok else "NO"} '
          f'-> {"PASS" if ok4 else "FAIL"}')
    lbl = lambda i: f'X{i}' if i < 7 else f'C{i-6}'
    ed_str = ', '.join(f'{lbl(a)}{lbl(b)}:{t}' for (a, b), t in
                       sorted(edges, key=lambda e: e[0]))
    print(f'      edge list: {ed_str}')

    # (5) 6-coloring cap check on the exact edge list
    from pysat.solvers import Cadical195
    K = 6
    n = 12
    slots = fslots
    def base_cnf():
        cls = []
        for v in range(n):
            cls.append([v*K+c+1 for c in range(K)])
            for c1 in range(K):
                for c2 in range(c1+1, K):
                    cls.append([-(v*K+c1+1), -(v*K+c2+1)])   # at-most-one
        for u, v in E:
            for c in range(K):
                cls.append([-(u*K+c+1), -(v*K+c+1)])
        return cls
    unsat_all = True
    n_subsets = 0
    for sub in itertools.combinations(range(len(slots)), 6):
        n_subsets += 1
        cls = base_cnf(); nv = n*K
        for si in sub:
            a, b = slots[si]; ys = []
            for c in range(K):
                nv += 1; y = nv
                cls.append([-y, a*K+c+1]); cls.append([-y, b*K+c+1])
                ys.append(y)
            cls.append(ys)                 # some colour is shared
        with Cadical195(bootstrap_with=cls) as s:
            if s.solve():
                unsat_all = False
                print(f'      SAT (!) for slot subset {sub}')
    # tightness: some 5-subset achievable
    sat5 = None
    for sub in itertools.combinations(range(len(slots)), 5):
        cls = base_cnf(); nv = n*K
        for si in sub:
            a, b = slots[si]; ys = []
            for c in range(K):
                nv += 1; y = nv
                cls.append([-y, a*K+c+1]); cls.append([-y, b*K+c+1])
                ys.append(y)
            cls.append(ys)
        with Cadical195(bootstrap_with=cls) as s:
            if s.solve():
                sat5 = sub; break
    results['5. cap check (all 462 six-subsets UNSAT)'] = unsat_all
    print(f'  [5] proper-6-colouring cap: {n_subsets} six-subsets of the 11 '
          f'r-slots all UNSAT: {"yes" if unsat_all else "NO"} '
          f'-> {"PASS" if unsat_all else "FAIL"}')
    print(f'      tightness: 5 mono slots achievable? '
          f'{"yes, e.g. slots "+str(sat5) if sat5 else "no 5-subset SAT"} '
          f'=> max mono = {5 if unsat_all and sat5 else "?"} / 11 < 1/2')

    print(f'  cosA = {sp.sstr(cosA)}')
    print(f'  sinA = {sp.sstr(sinA)}')
    print(f'  cosB = {sp.sstr(cosB)}')
    print(f'  sinB = {sp.sstr(sinB)}')
    return results

resA = run_chain(
    'A', 'chain12.json',
    gens=(S, w2, w7, w3),
    rels=[S**2 - 9 - 4*w3, w2**2 - 2, w7**2 - 7, w3**2 - 3],
    numsubs={S: sqrt(9+4*sqrt(3)), w2: sqrt(2), w7: sqrt(7), w3: sqrt(3)},
    r=w2, cos1=Ra(3, 4), sin1=w7/4, cosd=(2-w3)/4, sind=S/4,
    long_target=2+w3,
    prim_elt=sqrt(2)+sqrt(3)+sqrt(7)+sqrt(9+4*sqrt(3)), expect_deg=16)

resB = run_chain(
    'B', 'chain12b.json',
    gens=(T, w7, w3),
    rels=[T**2 - 9 + 4*w3, w7**2 - 7, w3**2 - 3],
    numsubs={T: sqrt(9-4*sqrt(3)), w7: sqrt(7), w3: sqrt(3)},
    r=1+w3, cos1=(2+w3)/4, sin1=T/4, cosd=Ra(3, 4), sind=w7/4,
    long_target=sp.Integer(1),
    prim_elt=sqrt(3)+sqrt(7)+sqrt(9-4*sqrt(3)), expect_deg=8)

print('=' * 78)
allok = all(resA.values()) and all(resB.values())
print('OVERALL:', 'ALL PASS' if allok else 'FAILURES PRESENT')
for nm, res in (('A', resA), ('B', resB)):
    for k, v in res.items():
        print(f'  chain {nm}: {k}: {"PASS" if v else "FAIL"}')
