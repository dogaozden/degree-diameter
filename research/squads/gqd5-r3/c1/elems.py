import sys, numpy as np, collections
sys.argv = ['x', '/home/user/degree-diameter/research/squads/gqd5-r3/c1/H1.npy']
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c1')
import orbsat2 as O
H = O.H; n = O.n
idp = np.arange(n)
def order(g):
    k = 1; c = g.copy()
    while not np.array_equal(c, idp): c = g[c]; k += 1
    return k
ords = [order(g) for g in H]
print(collections.Counter(ords))
for want in (2, 3, 4):
    idx = [i for i, o in enumerate(ords) if o == want][:3]
    print('order', want, 'indices', idx)
