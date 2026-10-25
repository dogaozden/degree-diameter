# independent BFS check of the best cyclic lift costs (c8): unreached lift vertices from each base source within D=8
import sys
from collections import deque
def lift_unreached(E, V, m, k, D):
    adj = {}
    for y in range(k):
        for g in range(m):
            adj[(y, g)] = []
    for i, (w, b, a) in enumerate(E):
        for g in range(m):
            adj[(w, g)].append((b, (g + V[i]) % m))
            adj[(b, (g + V[i]) % m)].append((w, g))
    tot = []
    for s in range(k):
        dist = {(s, 0): 0}; q = deque([(s, 0)])
        while q:
            x = q.popleft()
            if dist[x] >= D: continue
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; q.append(y)
        tot.append(k * m - len(dist))
    return tot, sum(tot)
m, D, k = 547, 8, 4
# base22 (gauge-fixed tree): edges (w,b,fixed) in file order; free edges are indices 1,3,4,5,7
E22 = [(0,2,1),(0,2,0),(0,3,1),(0,3,0),(1,2,0),(1,2,0),(1,3,1),(1,3,0)]
V22 = [0]*8
for idx, val in zip([1,3,4,5,7], [182, 435, 17, 516, 280]):
    V22[idx] = val
print('base22 best (cost per source, total):', lift_unreached(E22, V22, m, k, D))
# base31: free edges are indices 1,2,4,6,7 (voltages from RESULT line)
E31 = [(0,2,1),(0,2,0),(0,2,0),(0,3,1),(1,2,0),(1,3,1),(1,3,0),(1,3,0)]
V31 = [0]*8
for idx, val in zip([1,2,4,6,7], [315, 435, 225, 283, 289]):
    V31[idx] = val
print('base31 best (cost per source, total):', lift_unreached(E31, V31, m, k, D))
