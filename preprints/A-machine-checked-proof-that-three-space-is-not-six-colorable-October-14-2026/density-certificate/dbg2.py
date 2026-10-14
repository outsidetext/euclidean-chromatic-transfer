import sys, math
sys.argv=['x', sys.argv[1], '0']
exec(open('xcheck.py').read().split('if __name__')[0])
def Gf(t): return float(w0)+sum(w*math.sin(t*s)/(t*s) for w,s in zip(Wf,Sf))
def dGf(t): return sum(w*s*((t*s)*math.cos(t*s)-math.sin(t*s))/(t*s)**2 for w,s in zip(Wf,Sf))
c=274.95; ca=arb(c)
g=W0; g1=arb(0)
for s,w in zip(S,W):
    om,om1=om012(ca*s); g+=w*om; g1+=w*s*om1
print(g, Gf(c), g1, dGf(c))
print(sum(Wf), float(sum(terms[q] for q in qs)), Wf[:3], Sf[:3], [float(x.mid()) for x in S[:3]])
