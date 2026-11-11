"""Controller pair statistics for a coloured controller and a chart: for every same-side ordered pair (A side), its
controller distance and whether a nonsingular NB-4 walk exists.  usage: python3 pair_stats.py ctrl.edges chart"""
import sys, collections
from collections import deque
import build_lift_general as blg
from lift_check import load_chart, rank
from chart import mat_vec, mat_inv
edges = [tuple(map(int, l.split()[:2])) for l in open(sys.argv[1]) if l.strip()]
m = max(a for a, b in edges) + 1
col = blg.colour(m, edges); A, bv = load_chart(sys.argv[2]); Ai = [mat_inv(M) for M in A]
cadj = [[] for _ in range(2 * m)]
for a, b, c in col: cadj[a].append((m + b, c)); cadj[m + b].append((a, c))
stats = collections.Counter()
for u in range(m):
    d = [-1] * (2 * m); d[u] = 0; dq = deque([u])
    while dq:
        x = dq.popleft()
        for y, c in cadj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    ok = set(); anynb = set()
    for (b1, c1) in cadj[u]:
        for (w, c2) in cadj[b1]:
            if c2 == c1: continue
            for (b2, c3) in cadj[w]:
                if c3 == c2: continue
                for (t, c4) in cadj[b2]:
                    if c4 == c3: continue
                    anynb.add(t)
                    if t in ok: continue
                    vv = [mat_vec(Ai[c2], bv[c1]), mat_vec(Ai[c2], bv[c2]), mat_vec(Ai[c3], bv[c3]), mat_vec(Ai[c3], bv[c4])]
                    if rank(vv) == 4: ok.add(t)
    for v in range(m):
        stats[(d[v], v in anynb, v in ok)] += 1
print('A-side ordered pairs by (controller distance, has NB-4 walk, has nonsingular NB-4 walk):')
for k in sorted(stats): print(' ', k, stats[k])
