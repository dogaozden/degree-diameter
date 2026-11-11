# L = A-targets that become distance >5 from a* after deleting (a*, b); which B-vertices w have Ball3(w) containing L?
import numpy as np
from collections import deque
from graph import load
n, adj, E = load('base.e'); nA = 15730
C = np.load('C3.npy')                  # C[b_idx, a] = dist_base(a, b) <= 3
astar = 0; b = adj[astar][0]
# BFS from a* with edge (a*,b) removed
d = [-1] * n; d[astar] = 0; q = deque([astar])
while q:
    x = q.popleft()
    for y in adj[x]:
        if x == astar and y == b: continue
        if d[y] < 0: d[y] = d[x] + 1; q.append(y)
L = [v for v in range(nA) if d[v] < 0 or d[v] > 5]
print('lost A-targets', len(L))
bidx = b - nA
rows = C[:, L]                         # coverage of L by each B-centre
cover = rows.sum(axis=1)
order = np.argsort(-cover)[:10]
print('best B-centres cover of L:', [(int(i), int(cover[i])) for i in order])
print('b itself covers', int(cover[bidx]), 'of', len(L))
