from flint import arb, ctx
ctx.prec=100
pi=arb.pi()
# rho >= -min J0: J0 min at first zero of J1 (~3.8317); bracket j_{1,1} and bound J0 on bracket
j11=arb("3.83170597020751231561443588630816076656454")
print("min J0 ~", j11.bessel_j(0), " rho=0.40276 ok:", -j11.bessel_j(0) < arb("0.40276"))
# rigorous global: min J0 over [0,inf) = J0(j11); J0 on [3.8,3.86] min via value at j11 is enough since J0'=-J1 zero there and J0''>0.
print("min sinc ~", None)
x=arb("4.49340945790906417530788092728")  # first positive root of tan x = x
print("min sin x/x ~", x.sin()/x, " rho3=0.21724 ok:", -(x.sin()/x) < arb("0.21724"))
def case(name,d,A,a,b,rho,env,quad):
    d,A,a,b,rho=map(arb,(d,A,a,b,rho))
    c1 = 1 - rho*a - b*env(d*A)
    c2 = 1 + a*quad(A) - rho*b
    print(f"{name}: case t>A: {c1}  case t<=A<dt: {c2}  1+a+b={1+a+b}")
env2=lambda y:(2/(pi*y)).sqrt(); q2=lambda A:1-A*A/4
env3=lambda y:1/y; q3=lambda A:1-A*A/6
case("R2 d>=1e4",  "1e4","0.3","2.1976","7.8131","0.40276",env2,q2)
case("R2 d>=1e10","1e10","0.05","2.4794","8.6317","0.40276",env2,q2)
case("R3 d>=1e4",  "1e4","0.3","4.5595","25.2703","0.21724",env3,q3)
