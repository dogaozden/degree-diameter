import sys, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d8/d2')
import build_d2 as B
NW, E, arcs, H = B.build_base(1)
adj = [[] for _ in range(NW)]
for u, v, _ in E: adj[u].append(v); adj[v].append(u)
hist = collections.Counter()
for s in range(NW):
    d = [-1]*NW; d[s] = 0; q = [s]
    for x in q:
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x]+1; q.append(y)
    hist.update(d)
tot = sum(hist.values())
print('distance histogram over ordered pairs:', sorted(hist.items()))
