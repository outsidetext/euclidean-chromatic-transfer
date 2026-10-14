import numpy as np
from scipy.special import j0
def om3(x): return np.sinc(x/np.pi)
for name, f, q, lam, v in [("R2", j0, 32.0, 1.75, 1.25), ("R3", om3, 8.0, 2.24, 1.99)]:
    for K in [1,2,4,6,8,10]:
        w = v*lam**np.arange(K); D = q**np.arange(K)
        worst = 1e9
        for e in np.arange(-np.log10(D[-1])-3, 3, 0.05):
            t = np.geomspace(10**e, 10**(e+0.05), 4001)
            worst = min(worst, (1 + f(np.outer(t, D)) @ w).min())
        print(f"{name} q={q:.0f} K={K} chi>={1+w.sum():.1f} min h={worst:.4f}")
