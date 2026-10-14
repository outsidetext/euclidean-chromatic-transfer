import numpy as np
from scipy.special import j0
x = np.linspace(0, 400, 4_000_001)
print("min J0(x)-(1-x^2/4):", (j0(x) - (1 - x**2/4)).min(), " min J0:", j0(x).min())
for q in [4096]:
    for K in [1,2,3,4,5]:
        v = 2.2*2.5**np.arange(K); D = q**np.arange(K, dtype=float)
        worst = 1e9
        for e in range(-2, 3*K+2):                      # t over log-scales 10^e..10^(e+1) relative to 1/q^j
            lo, hi = 10.0**(-4*K+e*4/3)/1, 10.0**(-4*K+(e+1)*4/3)
            t = np.geomspace(max(lo,1e-30), hi, 200001)
            h = 1 + (j0(np.outer(t, D)) @ v); worst = min(worst, h.min())
        t = np.linspace(1e-9, 60, 2_000_001); h = 1 + (j0(np.outer(t, D)) @ v); worst = min(worst, h.min())
        print(f"q={q} K={K} sum v={v.sum():.2f} chi>={1+v.sum():.1f} min h={worst:.4f}")
