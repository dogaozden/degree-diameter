#!/usr/bin/env python3
"""fillhub.py IN.sol OUT.sol: add hub edges in unused hub slots (each hub has at most 4 hub edges; adding edges never
lengthens a distance).  Greedy: an edge (line-side hub a, point-side hub b) is worth the number of new flag pairs
(a//H, b//H) it creates, with a bonus for flags that have coverage holes; ties broken by fewest existing pairs."""
import sys, collections
import numpy as np
import lns
S = lns.read_sol(sys.argv[1]); H = S['H']; F = S['F']; k = len(F)
hg = [int(x) for x in S['rows']['hubgraph']]
pairs = [(hg[e], hg[e + 1]) for e in range(0, len(hg), 2)]
cost, unc = lns.cover(F, S['sig'], S['hubadj'], listing=True)
holeflag = collections.Counter(i for i, side, t in unc)
print('before: edges', len(pairs), 'cover', cost, unc[:5])
deg = collections.Counter(); degb = collections.Counter()
for a, b in pairs: deg[a] += 1; degb[b] += 1
A = S['hubadj'].copy(); have = set(pairs)
while True:
    best = None
    for a in range(H * k):
        if deg[a] >= 4: continue
        for b in range(H * k):
            if degb[b] >= 4 or (a, b) in have: continue
            i, j = a // H, b // H
            gain = (0 if A[i, j] else 10) + 5 * (holeflag[i] + holeflag[j]) * (0 if A[i, j] else 1)
            gain -= 0.01 * (A[i].sum() + A[:, j].sum())
            if best is None or gain > best[0]: best = (gain, a, b)
    if best is None: break
    g, a, b = best; pairs.append((a, b)); have.add((a, b)); deg[a] += 1; degb[b] += 1; A[a // H, b // H] = True
S['rows']['hubgraph'] = [str(x) for ab in pairs for x in ab]
S['hubadj'] = A
cost2, unc2 = lns.cover(F, S['sig'], A, listing=True)
print('after: edges', len(pairs), 'cover', cost2, unc2[:5], 'flag pairs', int(A.sum()))
lns.write_sol(sys.argv[2], S, S['sig'], cost2)
