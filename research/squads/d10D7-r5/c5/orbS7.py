# c5: orbits of the (partial) stabiliser on S and on all points; element orders of a sample.
import numpy as np, sys, random
from collections import Counter
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from h7 import *
q, N, lines, coords = load_hex(HEX7)
S = np.array([int(x) for x in open('/home/user/degree-diameter/research/squads/d10D7-r4/c5/points_best.txt').read().split()])
pos = {int(p): i for i, p in enumerate(S)}
pw = 7 ** np.arange(7)
idx = np.full(7 ** 7, -1, dtype=np.int64); idx[coords @ pw] = np.arange(N)
INV = np.array([0, 1, 4, 5, 2, 3, 6])
mats = []
for l in open(sys.argv[1]):
    t = l.split()
    if len(t) == 49: mats.append(np.array(list(map(int, t))).reshape(7, 7))
print('matrices read', len(mats))
rng = random.Random(7)
gens = rng.sample(mats, min(int(sys.argv[2]), len(mats)))
def perm(M):
    Y = (coords @ M.T) % q
    nz = Y != 0; first = np.argmax(nz, axis=1); lead = Y[np.arange(N), first]
    Yn = (Y * INV[lead][:, None]) % q
    return idx[Yn @ pw]
perms = [perm(M) for M in gens]
# orbits on all points under the generated group (union-find over generator perms)
parent = np.arange(N)
def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]; x = parent[x]
    return x
for pm in perms:
    for x in range(N):
        a, b = find(x), find(pm[x])
        if a != b: parent[a] = b
roots = np.array([find(x) for x in range(N)])
cnt = Counter(roots.tolist())
orb_sizes_all = Counter(cnt.values())
print('orbits on all points (sample group):', sorted(orb_sizes_all.items()))
inS_orbit = Counter(roots[S].tolist())
print('orbits meeting S: sizes of orbit and |orbit cap S|:', sorted(Counter((cnt[r], inS_orbit[r]) for r in inS_orbit).items()))
