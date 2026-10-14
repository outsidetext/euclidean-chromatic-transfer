import xcheck, numpy as np, math
from flint import arb
sp = xcheck.build_table()
xcheck.ENV_XMAX = -xcheck.upf((2/(xcheck.PI*arb(xcheck.XMAX))).sqrt())
for (d1,d2,a,b) in [(7.0,7.35,0.79790955+0.07,4.26741116), (7.0,7.35,0.79790955,4.26741116*1.06), (1.77,1.8585,2.73526709,2.39138374+0.15), (7.0,12.0,0.79790955,4.26741116),(5.0,6.0,0.79790955,4.26741116)]:
    ok,info,nb = xcheck.check_row(sp,d1,d2,a,b,400.0,maxdepth=6)
    print("negative control", (d1,d2,round(a,5),round(b,5)), "ok=",ok, info if not ok else info[0], flush=True)
