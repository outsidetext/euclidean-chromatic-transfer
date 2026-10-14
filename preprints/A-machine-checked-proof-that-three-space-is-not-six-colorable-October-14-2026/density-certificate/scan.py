import sys, numpy as np
sys.argv=['x', sys.argv[1], '0']
exec(open('xcheck.py').read().split('if __name__')[0])
s=np.array(Sf); w=np.array(Wf); best=(-1,0); tops=[]
for lo in np.arange(0.5, 2806.2, 50.0):
    t=np.arange(lo, lo+50, 5e-4)
    x=np.outer(t,s); G=float(w0)+(np.sin(x)/x)@w
    i=G.argmax(); tops.append((G[i],t[i]))
    if G[i]>best[0]: best=(G[i],t[i])
print("float scan max", best, "mu", float(mu), "gap", float(mu)-best[0])
print(sorted(tops)[-5:])
