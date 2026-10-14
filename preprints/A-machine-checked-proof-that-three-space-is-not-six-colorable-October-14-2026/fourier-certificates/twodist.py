"""Uniform-in-d certificate h=1+a J0(t)+b J0(dt) (R^2) or Omega3 (R^3). Cases (A cutoff):
 t>A: 1 - rho*a - b*env(dA) ; t<=A<dt: 1 + a*(1-A^2/c) - rho*b ; dt<=A: positive."""
import numpy as np
from scipy.special import j0
def solve(rho, c, env, d, A):
    e1 = env(d*A)
    a = (1 - 0)/rho
    for _ in range(200):
        b = (1 + a*(1 - A*A/c))/rho
        a = (1 - b*e1)/rho
    return a, b
for name, rho, c, env, om in [("R2", 0.4027594, 4, lambda x: np.sqrt(2/(np.pi*x)), j0),
                              ("R3", 0.2172337, 6, lambda x: 1/x, lambda x: np.sinc(x/np.pi))]:
    for d, A in [(1e6,0.3),(1e10,0.05),(1e4,0.3)]:
        a, b = solve(rho*1.0001, c, env, d, A); a*=0.999; b*=0.999
        t = np.concatenate([np.geomspace(1e-14, 1e-2, 400001), np.linspace(1e-2, 60, 4000001)])
        h = 1 + a*om(t) + b*om(d*t)
        print(f"{name} d={d:.0e} A={A} a={a:.4f} b={b:.4f} chi>={1+a+b:.3f} min h(grid)={h.min():.5f}")
