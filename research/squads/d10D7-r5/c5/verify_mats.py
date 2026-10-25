import numpy as np, sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from h7 import *
q, N, lines, coords = load_hex(HEX7)
S = np.array([int(x) for x in open('/home/user/degree-diameter/research/squads/d10D7-r4/c5/points_best.txt').read().split()])
inS = np.zeros(N, bool); inS[S] = True
X = coords[S]
pw = 7 ** np.arange(7)
idx = np.full(7 ** 7, -1, dtype=np.int64); idx[coords @ pw] = np.arange(N)
INV = np.array([0, 1, 4, 5, 2, 3, 6])
mats = []
for l in open(sys.argv[1]):
    t = l.split()
    if len(t) == 49: mats.append(np.array(list(map(int, t))).reshape(7, 7))
print('complete matrices', len(mats))
rng = random.Random(1)
sample = rng.sample(range(len(mats)), min(3000, len(mats)))
ok_S = 0; ok_sim = 0; ratios_seen = []
Bx = Bmat(X, X, q)
for k in sample:
    M = mats[k]
    V = (X @ M.T) % q
    first = np.argmax(V != 0, axis=1)
    lead = V[np.arange(len(V)), first]
    Vn = (V * INV[lead][:, None]) % q
    pids = idx[Vn @ pw]
    if (pids < 0).any() or (~inS[pids]).any():
        continue
    ok_S += 1
    Bg = Bmat(Vn, Vn, q)
    nz = Bx != 0
    r = set((Bg[nz] * INV[Bx[nz]]) % q)
    if len(r) == 1: ok_sim += 1
    ratios_seen.append(r.pop() if len(r) == 1 else -1)
print('sampled', len(sample), 'maps mapping S into S:', ok_S, 'similitudes:', ok_sim)
from collections import Counter
print('multipliers', Counter(ratios_seen))
# distinctness
keys = set(tuple(m.flatten()) for m in mats)
print('distinct matrices', len(keys))
