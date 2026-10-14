"""Certify chi(R^2,{1,d}) >= target for ALL d in [dlo, dhi]: cover by intervals [d1,d2], one certificate
h(t)=1+a J0(t)+b J0(dt) (b>=0) each. For d in [d1,d2]: J0(dt) >= M(t) := min_{x in [d1 t,d2 t]} J0(x), computed
from a fine table for x<=XT (grid error 0.582*dx subtracted) and by -sqrt(2/(pi x1)) for x1 > XT.
Check h_lower(t) >= 0 on a t-grid (Lipschitz margin) for t<=T, and a tail bound beyond T.
Needs 1+a+b > target-1.   usage: interval_cert.py target dlo dhi"""
import sys, numpy as np
from scipy.special import j0
from scipy.optimize import linprog
target, dlo, dhi = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
XT = 2000.0
X = np.linspace(0, XT + 50, 20_500_001); JX = j0(X); dx = X[1]
lev = [JX]
while (1 << len(lev)) <= len(JX):
    p = lev[-1]; s = 1 << (len(lev)-1); lev.append(np.minimum(p[:-s], p[s:]))
def M(x1, x2):
    out = np.empty_like(x1)
    big = x1 > XT
    out[big] = -np.sqrt(2/(np.pi*x1[big]))
    sm = ~big
    if sm.any():
        a1, a2 = x1[sm], np.minimum(x2[sm], XT + 40)
        env = np.where(x2[sm] > XT + 40, -np.sqrt(2/(np.pi*(XT+40))), 1.0)
        i = np.floor(a1/dx).astype(np.int64); j = np.ceil(a2/dx).astype(np.int64)
        L = np.maximum(j-i+1, 1); k = np.floor(np.log2(L)).astype(np.int64)
        r = np.empty_like(a1)
        for kk in np.unique(k):
            m = k == kk; arr = lev[kk]
            r[m] = np.minimum(arr[i[m]], arr[j[m]-(1 << kk)+1])
        out[sm] = np.minimum(r - 0.582*dx, env)
    return out
def lp(d1, d2):
    t = np.concatenate([np.linspace(0, 3.0/d1, 20001), np.linspace(3.0/d1, 40, 40001)])
    A = -np.stack([j0(t), M(d1*t, d2*t)], axis=1)
    r = linprog([-1,-1], A_ub=A, b_ub=np.ones(len(t)), bounds=[(None,None),(0,None)], method="highs")
    return r.x if r.status == 0 else None
def verify(a, b, d1, d2):
    T = max(60.0, (2/np.pi)*((abs(a)+b/np.sqrt(d1))*1.5)**2)
    t1 = min(T, XT/d1)                                # fine region until d1 t > XT
    e1 = 1e-3/d2
    t = np.arange(0, t1, e1)
    h = 1 + a*j0(t) + b*M(d1*t, d2*t)
    ok1 = h.min() - (abs(a)*0.582 + b*0.582*d2)*e1 > 1e-6 if len(t) else True
    e2 = 1e-3
    t = np.arange(t1, T, e2)
    h = 1 + a*j0(t) + b*M(d1*t, d2*t)                 # here d1 t may exceed XT -> envelope
    ok2 = h.min() - (abs(a)*0.582)*e2 - b*0.5*np.sqrt(2/(np.pi*d1))*t1**-1.5*e2 > 1e-6 if len(t) else True
    tail = 1 - abs(a)*np.sqrt(2/(np.pi*T)) - b*np.sqrt(2/(np.pi*d1*T))
    return ok1 and ok2 and tail > 0
d = dlo; cover = []; ratio = 1.05
while d < dhi:
    d2 = min(dhi, d*ratio)
    x = lp(d, d2); ok = False
    if x is not None:
        a, b = x*0.98
        ok = (1 + a + b > target - 1) and verify(a, b, d, d2)
    if ok:
        cover.append((d, d2, a, b)); d = d2; ratio = min(1 + (ratio-1)*1.6, 3.0)
        if len(cover) % 20 == 0: print(f"  d={d:.4f} intervals={len(cover)}", flush=True)
    else:
        ratio = 1 + (ratio-1)/3
        if ratio < 1 + 1e-5: print(f"FAILED near d={d}", flush=True); break
else:
    print(f"CERTIFIED chi(R^2,{{1,d}}) >= {target} for all algebraic d in [{dlo},{dhi}] ({len(cover)} intervals)", flush=True)
    np.save(f"cover_t{target}_{dlo}_{dhi}.npy", np.array(cover))
