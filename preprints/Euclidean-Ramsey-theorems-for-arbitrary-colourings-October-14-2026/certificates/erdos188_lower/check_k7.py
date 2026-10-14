# Independent check (Claude) of the Erdos #188 k>=7 certificate in PROOF_k7.md.
import itertools, numpy as np
from fractions import Fraction as Fr
from scipy.special import j0, j1
def Q(s):
    s0,s1,s2,s3,s4,s5,s6=s
    return (-15+5*s0+15*(s1+s2+s3+s4+s5)+5*s6
      -5*(s0*s2+s4*s6+s0*s3+s3*s6+s0*s4+s2*s6)-(s0*s5+s1*s6)+5*s0*s6
      -14*(s1*s3+s3*s5+s1*s4+s2*s5)-2*s1*s5-10*s2*s4)
adm=[s for s in itertools.product((0,1),repeat=7)
     if all(not(s[i] and s[i+1]) for i in range(6)) and any(s[0:6]) and any(s[1:7])]
vals=[Q(s) for s in adm]
print("admissible",len(adm),"min Q",min(vals),"tight",sum(v==0 for v in vals))
Y=[Fr(-339,4),-48,-38,-12,-2,5]; lam=Fr(126,5); B=sum(Fr(y) for y in Y)
print("B",B, "disc", (85+lam)**2-4*15*(lam-B))
Yf=np.array([float(y) for y in Y]); n=np.arange(1,7)
h=lambda t: (Yf[None,:]*j0(np.outer(t,n))).sum(1)
L=float(sum(abs(y)*k for y,k in zip(Y,n)))   # |h'| <= sum |Y_n| n (|J1|<=1)
step=2e-5; T=30.0
mx=-1e9; t0=0.0
while t0<T:
    t=np.arange(t0,min(t0+1,T)+step,step); v=h(t); i=v.argmax()
    if v[i]>mx: mx,targ=v[i],t[i]
    t0+=1
print("grid max h",mx,"at",targ,"Lipschitz slack",L*step/2,"bound",mx+L*step/2,"< lam",float(lam))
tail=np.sqrt(2/np.pi)*sum(abs(float(y))/np.sqrt(k) for y,k in zip(Y,n))/np.sqrt(T)
print("tail bound for t>=30:",tail)
