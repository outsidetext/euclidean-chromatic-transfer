# Rigorous-by-Lipschitz check: S(t,k) = J0(t)+J0(k t)+J0((1+k)t) > -1 for all t>=0, k in [0,1].
# Tail: for t >= T0, |J0(t)|,|J0((1+k)t)| <= sqrt(2/(pi t)) and J0 >= -0.40276 (global min), so S >= -0.40276 - 2 sqrt(2/(pi T0)).
import numpy as np
from scipy.special import j0
J0MIN = -0.402759395702553   # min of J0 (at t ~ 3.8317); round down
T0 = 7.5
tail = J0MIN - 2*np.sqrt(2/(np.pi*T0)); print("tail bound for t>=T0:", tail, "> -1:", tail > -1)
ht, hk = 5e-4, 5e-4
t = np.arange(0, T0 + ht, ht); worst = 9; arg = None
MAXJ1 = 0.5819  # max |J1|
for k in np.arange(0, 1 + hk, hk):
    S = j0(t) + j0(k*t) + j0((1+k)*t); i = S.argmin()
    if S[i] < worst: worst, arg = S[i], (t[i], k)
Lt = MAXJ1*(1 + 1 + 2); Lk = 2*T0*MAXJ1
err = Lt*ht/2 + Lk*hk/2
print(f"grid min S = {worst:.6f} at t={arg[0]:.4f}, k={arg[1]:.4f}; Lipschitz error <= {err:.5f}; certified inf S >= {worst-err:.5f} > -1: {worst-err > -1}")
