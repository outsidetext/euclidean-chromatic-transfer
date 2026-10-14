# Certified region of triangles (a,b,1), a<=b<=1, a+b>=1 (scale: longest side 1) with inf_t S > -1,
# S = J0(a t)+J0(b t)+J0(t).  Tail t>=T0: S >= J0MIN - sqrt(2/(pi T0))*(1/sqrt(b)+1), b>=1/2.
import numpy as np
from scipy.special import j0
J0MIN = -0.402759395702553; MAXJ1 = 0.5819; T0 = 12.0
tail = J0MIN - np.sqrt(2/(np.pi*T0))*(np.sqrt(2) + 1); assert tail > -1; print("tail", tail)
ht = 1e-3; t = np.arange(0, T0 + ht, ht)
h = 0.005   # cell width in a and b
cells_ok = 0; cells_bad = 0; cells_total = 0; out = []
for a_c in np.arange(h/2, 1, h):
    for b_c in np.arange(h/2, 1, h):
        if not (a_c <= b_c + 1e-12): continue
        # cell [a_c-h/2,a_c+h/2]x[b_c-h/2,b_c+h/2] must meet the triangle region a<=b, a+b>=1
        if a_c + b_c + h < 1: continue
        cells_total += 1
        S = j0(a_c*t) + j0(b_c*t) + j0(t); m = S.min()
        err = 2*MAXJ1*T0*(h/2) + MAXJ1*(a_c + b_c + 1 + h)*ht/2
        ok = m - err > -1
        cells_ok += ok; cells_bad += (not ok); out.append((a_c, b_c, m, ok))
print(f"cells: {cells_total}, certified {cells_ok}, not certified {cells_bad}")
np.save("tri_map.npy", np.array(out))
bad = np.array([(a, b, m) for a, b, m, ok in out if not ok])
print("uncertified region: a in [%.3f, %.3f], b in [%.3f, %.3f]" % (bad[:,0].min(), bad[:,0].max(), bad[:,1].min(), bad[:,1].max()))
print("min-side/longest over uncertified cells >= %.3f" % (bad[:,0].min() - h/2))
