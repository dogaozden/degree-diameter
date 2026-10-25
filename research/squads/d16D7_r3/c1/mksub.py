#!/usr/bin/env python3
"""mksub.py QUOT WEIGHT OUTGRAPH OUTMAP: induced subgraph on quotient vertices of weight WEIGHT, all weights 1 (unweighted MIS)."""
import sys
q, wt, og, om = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
W = []; adj = []
with open(q) as f:
    n = int(f.readline())
    for i in range(n):
        a = list(map(int, f.readline().split()))
        W.append(a[0]); adj.append(a[2:2 + a[1]])
keep = [v for v in range(n) if W[v] == wt]
idx = {v: i for i, v in enumerate(keep)}
with open(og, 'w') as f:
    f.write('%d\n' % len(keep))
    for v in keep:
        nb = [idx[u] for u in adj[v] if u in idx]
        f.write('1 %d %s\n' % (len(nb), ' '.join(map(str, nb))))
with open(om, 'w') as f:
    for v in keep:
        f.write('%d\n' % v)
print('kept', len(keep), 'of', n)
