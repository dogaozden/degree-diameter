import sys, collections, subprocess
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d8/d2')
import build_d2b as BB
for matching in (False, True):
    NW, E, arcs, H = BB.build_B(1, matching)
    adj = [[] for _ in range(NW)]
    for u, v, _ in E: adj[u].append(v); adj[v].append(u)
    hist = collections.Counter()
    for s in range(NW):
        d = [-1]*NW; d[s] = 0; q = [s]
        for x in q:
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x]+1; q.append(y)
        hist.update(d)
    print('matching', matching, 'hist', sorted(hist.items()))
