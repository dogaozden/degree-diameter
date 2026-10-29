import sys, random, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c4')
from build3 import read_sol, build, write_edges, HEX
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
from hexload import load
from collections import Counter
q, N, LP, PL, X = load(HEX)
SOL = '/home/user/degree-diameter/research/frontier/sols/d7D7_hex5_mirror81_n23598.sol'
_, _, R, hub, Hn, HP, sig = read_sol(SOL)
da = Counter(a for a, b in hub); db = Counter(b for a, b in hub)
print('line-hub degrees', Counter(da[t] for t in range(Hn)), 'point-hub degrees', Counter(db[s] for s in range(HP)), 'edges', len(hub), len(set(hub)))
# hub graph distances (bipartite graph on hubs only)
import collections
adj = collections.defaultdict(list)
for a, b in hub: adj[('L', a)].append(('P', b)); adj[('P', b)].append(('L', a))
def bfs(s):
    d = {s: 0}; dq = collections.deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if y not in d: d[y] = d[x] + 1; dq.append(y)
    return d
dl = []; dp = []
for t in range(0, Hn, 1):
    d = bfs(('L', t))
    dl += [d[('L', u)] for u in range(Hn) if ('L', u) in d and u != t]
    dp += [d[('P', u)] for u in range(HP) if ('P', u) in d]
print('hub-graph same-side(L) distances max', max(dl), 'hub-graph L-to-P max', max(dp), 'components reach', len(bfs(('L',0))))
print('hub R-points-per-line-hub check: R[:5]', R[:5], 'sig of R[:5]', [int(sig[x]) for x in R[:5]])
