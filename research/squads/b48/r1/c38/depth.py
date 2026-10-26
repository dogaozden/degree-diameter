import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/tools')
import numpy as np, groups
T = groups.table('heis 11'); N = T.shape[0]
volt = [int(l.split()[3]) for l in open(sys.argv[1]) if l.startswith('e ')]
S = volt; inv = [int(np.where(T[g]==0)[0][0]) for g in range(N)]
# full lift BFS from (A,e) over 2N vertices
dist = -np.ones(2*N, int); dist[0] = 0; q = [0]
for v in q:
    side, x = (0, v) if v < N else (1, v-N)
    for s in S:
        w = (N + int(T[x, s])) if side == 0 else (int(T[x, inv[s]]))
        if dist[w] < 0: dist[w] = dist[v]+1; q.append(w)
import collections
print('dist histogram', sorted(collections.Counter(dist.tolist()).items()))
