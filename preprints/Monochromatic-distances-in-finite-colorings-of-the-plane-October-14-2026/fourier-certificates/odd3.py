import numpy as np
from scipy.optimize import linprog
def om(x): return np.sinc(x/np.pi)
for N in [4,16,64,256]:
    d=np.arange(1,2*N,2).astype(float)
    # Fejer weights c_j for P(u)=cos u F_N(2u)
    c=np.array([ (2-(2*j+1)/N) if j<N-1 else 1.0/N for j in range(N)])
    t=np.concatenate([np.linspace(1e-6,10,400001), np.geomspace(10,2000,200001)])
    G=np.zeros_like(t)
    for cj,dj in zip(c,d): G+=cj*om(dj*t)
    print(f"N={N} sum c={c.sum():.3f} min G={G.min():.4f}  => chi>= {1+N/(-G.min()):.1f} (claim 1+0.4N={1+0.4*N:.1f})")
    tt=np.linspace(1e-6,12,120001)
    res=linprog(-np.ones(N),A_ub=-om(np.outer(tt,d)),b_ub=np.ones(len(tt)),bounds=[(None,None)]*N,method="highs")
    print(f"   LP optimum chi>={1+res.x.sum():.1f}")
