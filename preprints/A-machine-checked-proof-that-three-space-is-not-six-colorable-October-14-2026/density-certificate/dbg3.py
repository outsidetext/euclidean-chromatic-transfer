import sys, math, time
sys.argv=['x', sys.argv[1], '0']
t0=time.time()
exec(open('xcheck.py').read().split('if __name__')[0])
print("setup", time.time()-t0)
t1=time.time()
for k in range(100): check_cell(100+k*0.01, 100+k*0.01+0.01)
print("100 cells", time.time()-t1)
print(run_range((66.5,68.5)))
print(run_range((1000.5,1002.5)))
