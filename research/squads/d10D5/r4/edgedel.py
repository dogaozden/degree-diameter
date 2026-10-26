#!/usr/bin/env python3
"""edgedel.py IN.edges STATE.sol C0.lift2.sol x L OUT.edges: delete the 6 lift edges of the ordinary flag (x, L) (x a
point, L a line through x, neither freed, L != sigma(x)), add hub z on the fibre of x and hub z' on the fibre of L,
the hub edge z - z', and up to 3 more hub edges each to existing hubs of the other side with spare degree (most
spare first).  For damage counting with failpairs.py."""
import sys, collections
import numpy as np, lns
fin, st, c0, x, L, fout = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
N = lns.N; M = 6
ls = open(fin).read().split(); n = int(ls[0]); E = [tuple(map(int, ls[i:i + 2])) for i in range(1, len(ls), 2)]
fx = set(range(6 * x, 6 * x + 6)); fL = set(range(6 * (N + L), 6 * (N + L) + 6))
E2 = [e for e in E if not ((e[0] in fx and e[1] in fL) or (e[1] in fx and e[0] in fL))]
assert len(E) - len(E2) == 6, len(E) - len(E2)
deg = collections.Counter(); adj = collections.defaultdict(set)
for a, b in E2: deg[a] += 1; deg[b] += 1; adj[a].add(b); adj[b].add(a)
lift = 2 * N * M
# hub sides: a hub adjacent to a point fibre is "line-side"; find side of existing hubs by a neighbour
side = {}
for h in range(lift, n):
    nb = next(iter(adj[h] & set(range(lift))))
    side[h] = 'Lside' if nb < N * M else 'Pside'
z, zp = n, n + 1
E2 += [(z, v) for v in sorted(fx)] + [(zp, v) for v in sorted(fL)] + [(z, zp)]
spareP = sorted([h for h in range(lift, n) if side[h] == 'Pside' and deg[h] < 10], key=lambda h: deg[h])
spareL = sorted([h for h in range(lift, n) if side[h] == 'Lside' and deg[h] < 10], key=lambda h: deg[h])
for h in spareP[:3]: E2.append((z, h)); deg[h] += 1
for h in spareL[:3]: E2.append((zp, h)); deg[h] += 1
with open(fout, 'w') as f:
    f.write('%d\n' % (n + 2))
    for a, b in E2: f.write('%d %d\n' % (a, b))
print('n', n + 2, 'spare point-side hubs', len(spareP), 'spare line-side hubs', len(spareL))
