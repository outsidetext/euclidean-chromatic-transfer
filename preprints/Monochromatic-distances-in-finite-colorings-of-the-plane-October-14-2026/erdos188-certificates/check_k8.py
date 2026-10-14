# Independent check (Claude) of certs_k8_strip2x12.json: brute-force all 2^m patterns with numpy bit ops,
# exact integer arithmetic for C1, float Bessel grid + Lipschitz for C2, exact C3.
import json, sys, math, numpy as np
from fractions import Fraction as Fr
from scipy.special import j0
certs=json.load(open(sys.argv[1])); K=int(sys.argv[2])
U=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
d2=lambda p,q:(p[0]-q[0])**2+(p[0]-q[0])*(p[1]-q[1])+(p[1]-q[1])**2
cov=[]
for ci,C in enumerate(certs):
    assert int(C['k'])==K
    lam=Fr(C['lam']); Z=Fr(0); A=Fr(0); Y={}
    for B in C['blocks']:
        pts=[tuple(p) for p in B['points']]; m=len(pts); idx={p:i for i,p in enumerate(pts)}
        edges=[(i,j) for i in range(m) for j in range(i+1,m) if d2(pts[i],pts[j])==1]
        aps=set()
        for p in pts:
            for u in U:
                ap=[(p[0]+t*u[0],p[1]+t*u[1]) for t in range(K)]
                if all(q in idx for q in ap): aps.add(sum(1<<idx[q] for q in ap))
        z=Fr(B['z']); a=[Fr(x) for x in B['a']]
        y={tuple(map(int,k.split(','))):Fr(v) for k,v in B['y'].items()}
        den=math.lcm(z.denominator,*[x.denominator for x in a],*[v.denominator for v in y.values()])
        zi=int(z*den); ai=np.array([int(x*den) for x in a],dtype=object)
        nvalid=0; minval=None
        CH=1<<20
        for start in range(0,1<<m,CH):
            s=np.arange(start,min(start+CH,1<<m),dtype=np.int64)
            ok=np.ones(len(s),bool)
            for i,j in edges: ok&=~(((s>>i)&1).astype(bool)&((s>>j)&1).astype(bool))
            for apm in aps: ok&=(s&apm)!=0
            s=s[ok]
            if len(s)==0: continue
            bits=((s[:,None]>>np.arange(m))&1).astype(np.int64)
            val=np.full(len(s),zi,dtype=np.int64)
            val+=bits@np.array([int(x) for x in ai],dtype=np.int64)
            for (i,j),v in y.items(): val+=int(v*den)*(bits[:,i]&bits[:,j])
            nvalid+=len(s); mv=val.min(); minval=mv if minval is None else min(minval,mv)
        assert abs(zi)+sum(abs(int(x)) for x in ai)+sum(abs(int(v*den)) for v in y.values())<2**62
        print(f" cert{ci}: {m} pts {len(aps)} APs {nvalid} valid patterns, min C1 = {minval}/{den}")
        assert minval>=0
        for (i,j),v in y.items(): D=d2(pts[i],pts[j]); Y[D]=Y.get(D,Fr(0))+v
        Z+=z; A+=sum(a)
    Ds=sorted(D for D in Y if Y[D]!=0); Yf=np.array([float(Y[D]) for D in Ds]); sq=np.sqrt(Ds)
    S=sum(abs(float(Y[D]))/D**0.25 for D in Ds); T=(2/math.pi)*(S/float(lam))**2*1.05+1
    M2=float(sum(abs(Y[D])*D for D in Ds)); step=2e-5; mx=-1e18; t0=0.0   # |h''|<=sum|Y_D| D since |J0''|<=1
    while t0<T:
        t=np.arange(t0,min(t0+0.5,T)+step,step); v=j0(np.outer(t,sq))@Yf; mx=max(mx,v.max()); t0+=0.5
    ub=mx+M2*step**2/8+1e-12; print(f" cert{ci}: T={T:.1f} max h ~ {mx:.6f}, bound {ub:.6f} vs lam {float(lam):.6f}")
    assert ub<float(lam)
    Bt=sum(Y.values()); assert Bt<=lam
    lo,hi=(Fr(x) for x in eval(C['claimed']) ) if isinstance(C['claimed'],str) else (Fr(C['claimed'][0]),Fr(C['claimed'][1]))
    q=lambda d:Z+A*d+Bt*d*d+lam*(d-d*d); c2,c1=Bt-lam,A+lam; P=[lo,hi]
    if c2!=0 and lo< -c1/(2*c2) <hi: P.append(-c1/(2*c2))
    assert all(q(p)<0 for p in P); cov.append((lo,hi)); print(f" cert{ci}: C3 ok on [{float(lo):.4f},{float(hi):.4f}]")
cov.sort(); x=Fr(0)
for lo,hi in cov: assert lo<=x; x=max(x,hi)
assert x>=1; print("INDEPENDENT CHECK PASSED for k =",K)
