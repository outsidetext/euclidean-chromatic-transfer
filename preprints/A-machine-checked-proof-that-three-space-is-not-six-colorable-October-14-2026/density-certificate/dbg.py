import sys, math
sys.argv=['x', sys.argv[1], '0']
exec(open('xcheck.py').read().split('if __name__')[0])
def Gf(t): return float(w0)+sum(w*math.sin(t*s)/(t*s) for w,s in zip(Wf,Sf))
for a,b in [(0.5,2.5),(10.5,12.5),(23.4,23.5),(274.9,275.0),(23.43,23.4310)]:
    print(a,b,check_cell(a,b), Gf((a+b)/2))
print(max(Gf(23.40+i*1e-5) for i in range(5000)), max(Gf(274.90+i*1e-5) for i in range(10000)))
print(len(S), M2)
