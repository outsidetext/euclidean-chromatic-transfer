import numpy as np
from scipy.special import j0
for N in [4,16,64,256,1024]:
    d = np.arange(1, 2*N, 2)
    t = np.linspace(1e-4, 8, 400000)
    S = np.zeros_like(t)
    for k in d: S += j0(k*t)
    i = S.argmin(); print(N, round(S.min(),4), round(S.min()/np.sqrt(N),4), "at t=", round(t[i],5), "N*t=", round(N*t[i],3))
