# Analysis of the 1782-vertex AS(9)+quadrics base graph for Z4 / Z2^2 voltage lifts.
# Counts non-backtracking (NB) walks: W_k = A W_{k-1} - (D-I) W_{k-2}, W_1 = A, W_2 = A^2 - D.
import json, numpy as np
from collections import Counter, deque
d = json.load(open('/home/user/degree-diameter/research/gq4x/graphs/as_w2_q9_n1782.json'))
E = d['output'][1]; n = 1782
adj = [[] for _ in range(n)]
for u, v in E:
    adj[u].append(v); adj[v].append(u)
side = [-1] * n; side[0] = 0; dq = deque([0])
while dq:
    u = dq.popleft()
    for v in adj[u]:
        if side[v] < 0:
            side[v] = 1 - side[u]; dq.append(v)
        else:
            assert side[v] != side[u]
side = np.array(side)
print('sides', Counter(side.tolist()))
A = np.zeros((n, n))
for u, v in E:
    A[u, v] = 1; A[v, u] = 1
deg = A.sum(1); D = np.diag(deg); I = np.eye(n)
W = {1: A, 2: A @ A - D}
W[3] = A @ W[2] - (D - I) @ W[1]
W[4] = A @ W[3] - (D - I) @ W[2]
W[5] = A @ W[4] - (D - I) @ W[3]
# exact distances up to 5
dist = np.full((n, n), 99, dtype=np.int32)
np.fill_diagonal(dist, 0)
seen = np.eye(n, dtype=bool); frontier = np.eye(n)
for k in range(1, 6):
    nxt = (frontier @ A) > 0
    new = nxt & ~seen
    dist[new] = k; seen |= new; frontier = new.astype(float)
print('distance histogram', Counter(dist.ravel().tolist()))
same = side[:, None] == side[None, :]
off = ~np.eye(n, dtype=bool)
# 1) closed NB 4-walks per vertex (= 2 x number of 4-cycles through x)
diag4 = np.round(np.diag(W[4])).astype(int)
print('closed NB 4-walks per vertex (2*C4):', Counter(diag4.tolist()))
# 2) same-side pairs at distance 4: NB 4-walk counts (= geodesic counts)
m4 = same & off & (dist == 4)
print('same-side d=4 pairs: #NB4 walks', Counter(np.round(W[4][m4]).astype(int).tolist()))
# 3) same-side pairs at distance 2
m2 = same & off & (dist == 2)
print('same-side d=2 pairs: #NB2', Counter(np.round(W[2][m2]).astype(int).tolist()),
      ' #NB4', Counter(np.round(W[4][m2]).astype(int).tolist()).most_common(6))
# 4) cross pairs
mc = (~same) & (dist > 0)
for dd in (1, 3):
    mm = (~same) & (dist == dd)
    print(f'cross d={dd}: #pairs {mm.sum()}  #NB3', Counter(np.round(W[3][mm]).astype(int).tolist()).most_common(6),
          ' #NB5 min/mean', np.round(W[5][mm]).min(), round(float(np.round(W[5][mm]).mean()), 2))
print('max distance', dist[dist < 99].max(), ' cross pairs at d=5:', int(((~same) & (dist == 5)).sum()))
print('same-side pairs at d=3 (should be 0):', int((same & (dist == 3)).sum()))
np.save('/home/user/degree-diameter/research/squads/r1-d11D5/c6/dist.npy', dist.astype(np.int8))
np.save('/home/user/degree-diameter/research/squads/r1-d11D5/c6/side.npy', side.astype(np.int8))
