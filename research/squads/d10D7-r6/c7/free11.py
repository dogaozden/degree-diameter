"""For a set S of H(11) point ids: how many points are opposite to ALL of S (free, could extend S)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r6/c7')
from common11 import load_hex, A7
q = 11
h = load_hex(q); C = h['C']; N = h['N']
S = np.array([int(x) for x in open(sys.argv[1]).read().split()], dtype=np.int64)
X = (C @ A7) % q
cnt = np.zeros(N, dtype=np.int64)          # number of s in S with B(p,s) == 0 (non-opposite)
for a in range(0, N, 20000):
    Bm = (X[a:a+20000] @ C[S].T) % q
    cnt[a:a+20000] = (Bm == 0).sum(1)
inS = np.zeros(N, bool); inS[S] = True
free = np.nonzero((cnt == 0) & (~inS))[0]
print('set size', len(S), 'free points (opposite to all of S, not in S):', len(free))
np.save(sys.argv[1] + '.free.npy', free)
