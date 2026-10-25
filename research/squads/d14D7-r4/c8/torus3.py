# c8: for an order-3 power w of a Singer-like element g (order 666), is B(x, w x) = 0 for every point x of E?
import sys
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c8')
import orth as O
from ord37 import order_of, mpow
rng = np.random.default_rng(1)
for t in range(4000):
    g = O.rand_elem(rng, int(rng.integers(3, 11)))
    o = order_of(g)
    if o is not None and o % 37 == 0:
        break
print("order of g:", o)
MU = (O.U @ O.M) % 11
for name, e in [("order-3 power", o // 3), ("order-37 power", o // 37)]:
    w = mpow(g, e)
    perm = O.perm_of(w)
    d = np.sum(MU * O.U[perm], axis=1) % 11          # B(x, w x) for each point x
    print(name, "frac of points with B(x,wx)=0:", round(float(np.mean(d == 0)), 4))
