import numpy as np
def om(x): return np.sinc(x/np.pi)   # sin x / x
q=256.0; lam=4.0; v0=4.0
for K in [1,2,3,4,5,6]:
    v=v0*lam**np.arange(K); D=q**np.arange(K)
    worst=1e9
    for e in np.linspace(-3*K-3, 3, 60*K+60):
        t=np.geomspace(10.0**e, 10.0**(e+0.1), 20001)
        h=1+(om(np.outer(t,D))@v); worst=min(worst,h.min())
    print(f"R3 q={q:.0f} K={K} chi>={1+v.sum():.1f} min h={worst:.4f}")
