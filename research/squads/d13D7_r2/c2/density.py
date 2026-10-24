# card c2: density of cross-direction compatibility for tangent directions (random sample of coset pairs)
import numpy as np
rng = np.random.default_rng(1)
q = 11
def P(x, y): return (2*x[...,2]*y[...,2] - (x[...,0]*y[...,3] + y[...,0]*x[...,3]) - (x[...,1]*y[...,4] + y[...,1]*x[...,4])) % q
def Qv(x): return (x[...,2]*x[...,2] - x[...,0]*x[...,3] - x[...,1]*x[...,4]) % q
sq = {1,3,4,5,9}
def test(u, w, n=400000):
    u = np.array(u); w = np.array(w)
    t = rng.integers(0, q, size=(n, 5)); s = rng.integers(0, q, size=(n, 5))
    d = (t - s) % q
    Pu = int(P(u, w)); Qu = int(Qv(u)); Qw = int(Qv(w))
    tang = (Pu*Pu - 4*Qu*Qw) % q == 0
    r = Pu * pow(2*Qu, q-2, q) % q if Qu else 0
    rho = (w - r*u) % q
    cond1 = P(d, rho) == 0
    A = P(d, u); C = Qv(d); D = (A*A - 4*Qu*C) % q
    cond2 = (D != 0) & np.isin(D, list(set(range(1,q)) - sq))
    return tang, (cond1 & cond2).mean(), (cond1 & cond2).sum()
tang, dens, cnt = test((1,0,0,9,0), (0,1,0,1,4))
print('tangent:', tang, 'cross-compatible density over random coset pairs: %.4f (1/22 = %.4f)' % (dens, 1/22))
tang2, dens2, _ = test((1,0,0,9,0), (1,0,0,9,0))
print('same direction density (should be 6710/14641 = %.4f): %.4f' % (6710/14641, dens2))
