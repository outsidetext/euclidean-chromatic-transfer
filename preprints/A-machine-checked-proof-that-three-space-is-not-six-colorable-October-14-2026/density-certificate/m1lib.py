"""LP machinery for upper bounds on m1(R^3) (unit-distance-avoiding density).

Normalisation: g(r) = radialised autocorrelation of 1_A divided by delta = dens(A), so g(0)=1,
g(1)=0.  g(r) = a0 + sum_k a_k Omega3(t_k r) + a_inf*[r==0],  a >= 0, sum a = 1, and a0 >= delta
(a0 = hat f(0)/delta >= delta).

For a finite configuration U = (x_1..x_N) the matrix delta*G, G_ij = g(|x_i-x_j|), is a convex
combination of 1_S 1_S^T (S subset of U) -- the pair marginals of A ∩ (random rigid motion of U).
Valid linear inequalities <Z, X> >= beta of that polytope give constraints
        sum_ij Z_ij G_ij >= beta/delta,
linear in a for fixed delta.  Constraints are stored as (dists, coeffs, beta) meaning
        sum_j coeffs_j g(dists_j) >= beta/delta     (dists may contain 0 -> g(0)=1).
"""
import itertools
import numpy as np
from scipy.optimize import linprog

def omega3(x):
    x = np.asarray(x, float)
    out = np.ones_like(x)
    nz = np.abs(x) > 1e-12
    out[nz] = np.sin(x[nz]) / x[nz]
    return out

def tgrid(T=200.0):
    a = np.arange(0.002, 20.0, 0.004)
    b = np.arange(20.0, 60.0, 0.01)
    c = np.arange(60.0, T, 0.05)
    return np.concatenate([a, b, c])

class Cons:
    def __init__(self, dists, coeffs, beta, tag=""):
        d = np.asarray(dists, float); c = np.asarray(coeffs, float)
        # merge equal distances
        key = np.round(d, 12)
        u, inv = np.unique(key, return_inverse=True)
        cc = np.zeros(len(u)); np.add.at(cc, inv, c)
        self.d, self.c, self.beta, self.tag = u, cc, float(beta), tag
    def row(self, t):
        """coefficients on [a0, a_k..., a_inf] of sum_j c_j g(d_j)."""
        r0 = self.c.sum()                      # a0 contributes 1 to every g(d)
        rk = (self.c[None, :] * omega3(np.outer(t, self.d))).sum(1)
        rinf = self.c[self.d == 0].sum()
        return np.concatenate([[r0], rk, [rinf]])
    def value(self, gfun):
        return float((self.c * gfun(self.d)).sum())

class M1LP:
    def __init__(self, T=200.0, t=None):
        self.t = tgrid(T) if t is None else t
        self.cons = []
        self.unitrow = Cons([1.0], [1.0], 0).row(self.t)
    def add(self, c):
        self.cons.append(c)
    def solve_fixed(self, delta):
        """max a0 subject to everything with delta fixed.  Returns (a0, a, duals) or None."""
        t = self.t; n = len(t) + 2
        obj = np.zeros(n); obj[0] = -1
        Aeq = np.vstack([np.ones(n), self.unitrow]); beq = np.array([1.0, 0.0])
        if self.cons:
            Aub = -np.vstack([c.row(t) for c in self.cons])
            bub = -np.array([c.beta / delta for c in self.cons])
        else:
            Aub = None; bub = None
        res = linprog(obj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=(0, None), method="highs")
        if res.status != 0:
            return None
        return -res.fun, res.x, res
    def solve(self, lo=0.05, hi=0.2, tol=1e-7):
        """sup{delta : max a0(delta) >= delta}."""
        if all(c.beta == 0 for c in self.cons):
            r = self.solve_fixed(1.0); return r[0], r
        best = None
        r = self.solve_fixed(hi)
        if r is not None and r[0] >= hi: return hi, r
        while hi - lo > tol:
            mid = 0.5 * (lo + hi)
            r = self.solve_fixed(mid)
            if r is not None and r[0] >= mid:
                lo, best = mid, r
            else:
                hi = mid
        if best is None: best = self.solve_fixed(lo)
        return lo, best
    def gfun(self, a):
        t = self.t
        def g(r):
            r = np.atleast_1d(np.asarray(r, float))
            out = a[0] + omega3(np.outer(r, t)) @ a[1:-1]
            out = out + a[-1] * (r == 0)
            return out
        return g

# ---------- correlation polytope separation ----------

def subsets_masks(N, edges=()):
    nb = [0] * N
    for i, j in edges:
        nb[i] |= 1 << j; nb[j] |= 1 << i
    out = []
    for m in range(1 << N):
        ok = True
        mm = m
        while mm:
            v = (mm & -mm).bit_length() - 1
            if nb[v] & m: ok = False; break
            mm &= mm - 1
        if ok: out.append(m)
    return out

def separate(X, delta, gfun, unit_tol=1e-9):
    """X: N x 3 points.  Find most violated inequality <Z, P> >= beta, |Z_ij|<=1, for P = delta*G.
    Pairs at unit distance are treated as edges (only independent S used; g=0 there).
    Returns (violation, Cons) where violation = beta - <Z,P> (positive = violated)."""
    X = np.asarray(X, float); N = len(X)
    D = np.sqrt(((X[:, None] - X[None]) ** 2).sum(-1))
    edges = [(i, j) for i in range(N) for j in range(i + 1, N) if abs(D[i, j] - 1) < unit_tol]
    masks = subsets_masks(N, edges)
    pairs = [(i, i) for i in range(N)] + [(i, j) for i in range(N) for j in range(i + 1, N)
                                          if abs(D[i, j] - 1) >= unit_tol]
    P = np.array([delta if i == j else delta * gfun([D[i, j]])[0] for i, j in pairs])
    # variables: z_p (len pairs), beta ; maximize beta - z.P  s.t. beta - z.v_S <= 0 for all S
    V = np.array([[1.0 if ((m >> i) & 1 and (m >> j) & 1) else 0.0 for (i, j) in pairs] for m in masks])
    npr = len(pairs)
    obj = np.concatenate([P, [-1.0]])          # minimise z.P - beta
    Aub = np.hstack([-V, np.ones((len(masks), 1))])
    bub = np.zeros(len(masks))
    bounds = [(-1, 1)] * npr + [(-npr, npr)]
    res = linprog(obj, A_ub=Aub, b_ub=bub, bounds=bounds, method="highs")
    z = res.x[:npr]; beta = res.x[-1]
    viol = -res.fun
    # constraint sum_p z_p g_p >= beta/delta, off-diagonal pairs counted once (symmetric Z: 2 Z_ij -> z_p)
    dists = [0.0 if i == j else D[i, j] for i, j in pairs]
    return viol, Cons(dists, z, beta, tag=f"N{N}")

def unit_edges(X, tol=1e-9):
    X = np.asarray(X, float); N = len(X)
    D = np.sqrt(((X[:, None] - X[None]) ** 2).sum(-1))
    return [(i, j) for i in range(N) for j in range(i + 1, N) if abs(D[i, j] - 1) < tol]

def domega3(x):
    x = np.asarray(x, float)
    out = np.zeros_like(x)
    nz = np.abs(x) > 1e-6
    xn = x[nz]
    out[nz] = (xn * np.cos(xn) - np.sin(xn)) / xn**2
    out[~nz] = -x[~nz] / 3.0
    return out

class GFun:
    """g and g' from an LP solution vector a on grid t (a0, a_k, a_inf)."""
    def __init__(self, t, a, thresh=1e-12):
        keep = a[1:-1] > thresh
        self.t = t[keep]; self.ak = a[1:-1][keep]; self.a0 = a[0]; self.ainf = a[-1]
    def __call__(self, r):
        r = np.atleast_1d(np.asarray(r, float))
        return self.a0 + omega3(np.outer(r, self.t)) @ self.ak + self.ainf * (r == 0)
    def d(self, r):
        r = np.atleast_1d(np.asarray(r, float))
        return domega3(np.outer(r, self.t)) @ (self.ak * self.t)

def separate_full(X, delta, g, edges=None):
    """Full correlation polytope COR(N) separation (no edge restriction unless edges given).
    Returns (viol, z over all pairs incl diag, beta, pairs, D)."""
    X = np.asarray(X, float); N = len(X)
    D = np.sqrt(((X[:, None] - X[None]) ** 2).sum(-1))
    edges = edges or []
    masks = subsets_masks(N, edges)
    eset = set(edges)
    pairs = [(i, i) for i in range(N)] + [(i, j) for i in range(N) for j in range(i + 1, N) if (i, j) not in eset]
    dv = np.array([0.0 if i == j else D[i, j] for i, j in pairs])
    P = delta * g(dv)
    P[:N] = delta
    V = np.array([[1.0 if ((m >> i) & 1 and (m >> j) & 1) else 0.0 for (i, j) in pairs] for m in masks])
    npr = len(pairs)
    obj = np.concatenate([P, [-1.0]])
    Aub = np.hstack([-V, np.ones((len(masks), 1))])
    res = linprog(obj, A_ub=Aub, b_ub=np.zeros(len(masks)), bounds=[(-1, 1)] * npr + [(-4 * npr, 4 * npr)], method="highs")
    return -res.fun, res.x[:npr], res.x[-1], pairs, dv

_VCACHE = {}
def _vmat(N, pairs_key, pairs, masks):
    k = (N, pairs_key)
    if k not in _VCACHE:
        _VCACHE[k] = np.array([[1.0 if ((m >> i) & 1 and (m >> j) & 1) else 0.0 for (i, j) in pairs] for m in masks])
    return _VCACHE[k]

def separate_ratio(X, delta, g, edges=()):
    """max (beta - z.P) s.t. z.v_S >= beta for all (independent) S, z.Pref - beta = 1,
    Pref = Bernoulli(delta) product point.  Value > 0 iff P = delta*G is outside COR."""
    X = np.asarray(X, float); N = len(X)
    D = np.sqrt(((X[:, None] - X[None]) ** 2).sum(-1))
    edges = tuple(edges); eset = set(edges)
    masks = subsets_masks(N, edges)
    pairs = [(i, i) for i in range(N)] + [(i, j) for i in range(N) for j in range(i + 1, N) if (i, j) not in eset]
    dv = np.array([0.0 if i == j else D[i, j] for i, j in pairs])
    P = delta * g(dv); P[:N] = delta
    if edges:
        # reference: product measure conditioned on independence -> use average of independent-set vertices
        V = _vmat(N, edges, pairs, masks)
        Pref = V.mean(0) * 0.5 + 0.5 * V[0]   # interior-ish point (mixture incl. empty set)
    else:
        V = _vmat(N, (), pairs, masks)
        Pref = np.full(len(pairs), delta * delta); Pref[:N] = delta
    npr = len(pairs)
    obj = np.concatenate([P, [-1.0]])                     # minimise z.P - beta
    Aub = np.hstack([-V, np.ones((len(masks), 1))])
    Aeq = np.concatenate([Pref, [-1.0]])[None, :]
    res = linprog(obj, A_ub=Aub, b_ub=np.zeros(len(masks)), A_eq=Aeq, b_eq=[1.0],
                  bounds=[(None, None)] * (npr + 1), method="highs")
    if res.status != 0:
        return -1.0, np.zeros(npr), 0.0, pairs, dv
    return -res.fun, res.x[:npr], res.x[-1], pairs, dv
