import sys, time; sys.path.insert(0,'/home/user/degree-diameter/research/squads/b48/r3/d15')
import numpy as np, random
from grp_mat import make_group
from coset import subgroups4, build_nbr, bfs
t=time.time()
N,mul = make_group('PGL',23)
print("PGL(2,23) order", N, time.time()-t)
# associativity / identity sanity
rng=np.random.default_rng(1)
x=rng.integers(0,N,2000); y=rng.integers(0,N,2000); z=rng.integers(0,N,2000)
assert np.all(mul(mul(x,y),z)==mul(x,mul(y,z)))
assert np.all(mul(x,0)==x) and np.all(mul(0,x)==x)
print("assoc ok", time.time()-t)
subs=subgroups4(N,mul)
print("order-4 subgroups", len(subs), time.time()-t)
