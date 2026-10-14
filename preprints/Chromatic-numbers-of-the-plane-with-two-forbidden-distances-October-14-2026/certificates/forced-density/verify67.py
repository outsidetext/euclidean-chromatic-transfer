"""Record-grade verification of  p_{1/sqrt3} >= 1/67.

Claim: there is a 30-point set in Q(sqrt3,sqrt5) such that, with sqrt3 as the forbidden
distance, the graph formed by all its sqrt3-pairs together with a set S of only 67
distance-1 pairs is NOT properly 5-colorable, and S is minimal (every proper subset is
5-colorable).  Hence in every 5-coloring of the plane at least one pair of S is mono, so
the invariant forced density satisfies p_{1/sqrt3} >= 1/67, improving 1/72.

Checks performed:
  1. every pair of S is EXACTLY at distance 1, and every forbidden edge EXACTLY at sqrt3
     (integer arithmetic: 64 d^2 = (rat, irr), d=1 <=> (64,0), d=sqrt3 <=> (192,0));
  2. the sqrt3-pairs used are ALL sqrt3-pairs present in the point set (nothing hidden);
  3. non-5-colorability: Glucose with a DRAT proof (checked by drat-trim if available)
     + independent CaDiCaL cross-check;
  4. minimality of S: removing any single pair restores 5-colorability.

Usage:  python3 verify67.py [record67_graph.json] [path/to/drat-trim]
drat-trim is taken from the second argument, else from the environment variable
DRAT_TRIM, else from the PATH.  The script writes record67.cnf and record67.drat to the
current directory (so run it from a scratch directory if you want to keep the shipped
copies untouched).
"""
import json, sys, subprocess, os, shutil
from pysat.solvers import Cadical153, Glucose42

K = 5
D = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "record67_graph.json"))
U = [tuple(v) for v in D["univ"]]
S = [tuple(e) for e in D["S"]]
n = len(U)
print(f"points: {n}   designated 1-pairs |S| = {len(S)}")


def cls(u, v):
    d0, d1, d2, d3 = u[0]-v[0], u[1]-v[1], u[2]-v[2], u[3]-v[3]
    irr = 2*d0*d1 + 6*d2*d3
    rat = d0*d0 + 5*d1*d1 + 3*d2*d2 + 15*d3*d3
    if irr != 0:
        return None
    return 1 if rat == 64 else (3 if rat == 192 else None)


# ---- 1 & 2: exact geometry ----
bad = [e for e in S if cls(U[e[0]], U[e[1]]) != 1]
if bad:
    sys.exit(f"FAIL: {len(bad)} designated pairs are not at exact distance 1")
E3 = [(i, j) for i in range(n) for j in range(i+1, n) if cls(U[i], U[j]) == 3]
print(f"exact check: all {len(S)} designated pairs at distance 1 = (64,0)  OK")
print(f"exact check: {len(E3)} forbidden pairs at distance sqrt3 = (192,0), ALL present  OK")
if len(set(S)) != len(S):
    sys.exit("FAIL: duplicate designated pairs")


def var(v, c): return v*K + c + 1


def cnf_for(Sset):
    cl = []
    for v in range(n):
        cl.append([var(v, c) for c in range(K)])
        for c1 in range(K):
            for c2 in range(c1+1, K):
                cl.append([-var(v, c1), -var(v, c2)])
    for (u, v) in list(E3) + list(Sset):
        for c in range(K):
            cl.append([-var(u, c), -var(v, c)])
    return cl


# ---- 3: non-5-colorability + DRAT ----
cl = cnf_for(S)
# NOTE: use Glucose for the DRAT proof.  pysat's CaDiCaL emits a proof that drat-trim
# rejects (an incremental-solving artifact -- it does not end in the empty clause and
# appending one does not repair it).  Glucose's proof verifies cleanly.
s = Glucose42(bootstrap_with=cl, with_proof=True)
sat = s.solve()
proof = s.get_proof() if not sat else None
s.delete()
if sat:
    sys.exit("FAIL: instance is 5-colorable")
print("Glucose: UNSAT (non-5-colorable)  OK")

g = Cadical153(bootstrap_with=cl)
sat2 = g.solve(); g.delete()
print(f"CaDiCaL cross-check: {'UNSAT  OK' if not sat2 else 'SAT  ** DISAGREE **'}")
if sat2:
    sys.exit("FAIL: solver disagreement")

nv = n*K
with open("record67.cnf", "w") as f:
    f.write(f"p cnf {nv} {len(cl)}\n")
    for c in cl:
        f.write(" ".join(map(str, c)) + " 0\n")
with open("record67.drat", "w") as f:
    f.write("\n".join(proof) + "\n")
print(f"wrote record67.cnf ({len(cl)} clauses) and record67.drat ({len(proof)} lines)")

dt = (sys.argv[2] if len(sys.argv) > 2 else None) or os.environ.get("DRAT_TRIM") \
    or shutil.which("drat-trim")
if dt and os.path.exists(dt):
    r = subprocess.run([dt, "record67.cnf", "record67.drat"],
                       capture_output=True, text=True, errors="replace", timeout=1800)
    out = (r.stdout or "") + (r.stderr or "")
    tail = [l for l in out.splitlines() if l.startswith("s ")]
    print("drat-trim:", tail[-1] if tail else "no 's' line in drat-trim output")
else:
    print("drat-trim not found: skipping the DRAT check.  Pass its path as the second "
          "argument, set DRAT_TRIM, or put drat-trim on the PATH "
          "(https://github.com/marijnheule/drat-trim); or run "
          "'drat-trim record67.cnf record67.drat' yourself.")

# ---- 4: minimality ----
print("checking minimality of S ...")
nonmin = []
for k, e in enumerate(S):
    sub = S[:k] + S[k+1:]
    sv = Cadical153(bootstrap_with=cnf_for(sub))
    ok = sv.solve(); sv.delete()
    if not ok:
        nonmin.append(e)
if nonmin:
    print(f"** S is NOT minimal: {len(nonmin)} removable pairs **")
else:
    print(f"minimality: all {len(S)} pairs are necessary  OK")

print()
print(f"RESULT   p_{{1/sqrt3}} >= 1/{len(S)} = {1/len(S):.9f}   (previous 1/72 = {1/72:.9f})")
print(f"cap = 1/3; win needs |S| <= 2")
