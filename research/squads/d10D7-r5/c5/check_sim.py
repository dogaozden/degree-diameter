import numpy as np, sys
q = 7
J = np.zeros((7, 7), dtype=np.int64)
for a, b in [(0, 4), (1, 5), (2, 6)]:
    J[a, b] = 1; J[b, a] = 1
J[3, 3] = -2
mats = []
for l in open(sys.argv[1]):
    t = l.split()
    if len(t) == 49: mats.append(np.array(list(map(int, t))).reshape(7, 7))
from collections import Counter
cnt = Counter()
for M in mats[:20000]:
    G = (M.T @ J @ M) % q
    # proportional to J?
    c = None; okc = True
    nzJ = J % q != 0
    if not np.all((G[nzJ] * pow(1, 1, q)) % q == 0) and False: pass
    ratio = set(((G[nzJ] * 1) % q * 1).tolist())
    # check G == c*J mod q
    cand = [c for c in range(1, q) if np.array_equal(G % q, (c * J) % q)]
    cnt[len(cand) > 0] += 1
print('similitude (M^T J M = c J) count among first 20000:', cnt)
