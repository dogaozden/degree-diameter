"""List uncovered same-side controller pairs (chart-aware rule of mlift_chart) for a coloured controller edge list
"a b colour" and a pattern file.  usage: python3 uncovered.py ctrl.edges patterns"""
import sys, collections
from collections import deque
rows = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
m = max(r[0] for r in rows) + 1
sing = {}
for l in open(sys.argv[2]):
    s, a, b, c, d, r = l.split(); sing[(s, int(a), int(b), int(c), int(d))] = int(r) < 4
adj = [[] for _ in range(2 * m)]
for a, b, c in rows: adj[a].append((m + b, c)); adj[m + b].append((a, c))
out = collections.Counter(); examples = []
for side, rng in (('A', range(m)), ('B', range(m, 2 * m))):
    for u in rng:
        cov = set()
        for (x, c1) in adj[u]:
            for (y, c2) in adj[x]:
                if y != u: cov.add(y)
        for (x, c1) in adj[u]:
            for (y, c2) in adj[x]:
                if c2 == c1: continue
                for (z, c3) in adj[y]:
                    if c3 == c2: continue
                    for (t, c4) in adj[z]:
                        if c4 == c3: continue
                        if not sing[(side, c1, c2, c3, c4)]: cov.add(t)
        d = {u: 0}; dq = deque([u])
        while dq:
            x = dq.popleft()
            for (y, c) in adj[x]:
                if y not in d: d[y] = d[x] + 1; dq.append(y)
        for t in rng:
            if t not in cov:
                out[(side, d.get(t))] += 1
                if len(examples) < 8: examples.append((side, u, t, d.get(t)))
print('uncovered ordered pairs by (side, controller distance):', dict(out))
print('examples (side, source, target, distance):', examples)
