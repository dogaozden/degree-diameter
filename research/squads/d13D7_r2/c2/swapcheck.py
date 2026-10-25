# card c2: tightness of affine points w.r.t. a line-clique T = union of lines t+F11*u (affine chart of H(11)),
# and search for (1,2)-swaps: remove one line-point t, insert two mutually compatible points that conflict only with t.
import numpy as np, itertools, sys
q = 11
u = np.array([1, 0, 0, 9, 0])
def Qv(X):  # X: (...,5) array, Q(a,b,c,e,f) = c^2 - a e - b f
    return (X[..., 2] * X[..., 2] - X[..., 0] * X[..., 3] - X[..., 1] * X[..., 4]) % q
offs = [list(map(int, s.split()))[1:] for s in open(sys.argv[1]) if s.strip() and not s.startswith('#')]
T = []
for t in offs:
    t = np.array(t)
    for lam in range(q):
        T.append((t + lam * u) % q)
T = np.array(T)
print('affine points in T:', len(T))
allp = np.array(list(itertools.product(range(q), repeat=5)))
tight = np.zeros(len(allp), dtype=int)
owner = np.full(len(allp), -1)
for k, t in enumerate(T):
    z = Qv((allp - t) % q) == 0
    tight += z
    owner[z & (owner < 0)] = k
inT = np.zeros(len(allp), bool)
key = {tuple(p): i for i, p in enumerate(allp)}
for t in T:
    inT[key[tuple(t)]] = True
free = (~inT)
print('tightness distribution (outside T):', np.bincount(tight[free])[:6])
one = np.where(free & (tight == 1))[0]
print('1-tight points:', len(one))
# group 1-tight points by owner t
from collections import defaultdict
L = defaultdict(list)
for i in one:
    L[owner[i]].append(i)
found = 0
for k, lst in L.items():
    for a, b in itertools.combinations(lst, 2):
        if Qv((allp[a] - allp[b]) % q) != 0:
            found += 1
            if found <= 3: print('(1,2)-swap at line point', T[k], 'insert', allp[a], allp[b])
print('(1,2)-swap candidates:', found)
