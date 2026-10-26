#!/usr/bin/env python3
"""build_fd.py GQBIN SOL "FDSET" OUT.edges: rebuild the graph of the FLAGDEL hub construction independently of dmhub2.c.

Doubled-matching Z6-lift of W(q) (vertex (x, h) = 6x + h, points x < N, lines N + l), minus the 12 jump edges of each
freed point p_i; for flags i in FDSET also minus the 6 lift edges of the flag (p_i, sigma(p_i)).  Hubs: per freed
flag, H_i line-side hubs joined to the whole fibre of p_i and H_i point-side hubs joined to the fibre of sigma(p_i),
H_i = 3 for i in FDSET, else 2 (the third hub of other flags does not exist).  Hub edges from the "hubgraph" line
(pairs a b: line-side hub a = 3i + t, point-side hub b = 3j + u).  Hubs are numbered compactly after the lift.
"""
import sys, struct

gq, solf, fds, out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
with open(gq, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    Q1 = q + 1
    pts = struct.unpack('%di' % (L * Q1), f.read(4 * L * Q1))
rows = {}
for ln in open(solf):
    t = ln.split()
    if t: rows[t[0]] = t[1:]
free = [int(x) for x in rows['free']]
sig = [int(x) for x in rows['sigma']]
mv0 = [int(x) for x in rows['mv0']]; mv1 = [int(x) for x in rows['mv1']]
nu = [int(x) for x in rows['nu']]
hg = [int(x) for x in rows.get('hubgraph', [])]
assert int(rows['dmhub'][3]) == 3, 'expects H = 3 numbering'
FD = set(int(x) for x in fds.split())
M = 6
isfree = set(free)
fdflag = {(free[i], sig[free[i]]) for i in FD}
E = []
for l in range(N):
    for k in range(Q1):
        p = pts[l * Q1 + k]
        if (p, l) in fdflag: continue
        g = nu[l * Q1 + k]
        for h in range(M): E.append((p * M + h, (N + l) * M + (h + g) % M))
for p in range(N):
    if p in isfree: continue
    for h in range(M):
        E.append((p * M + h, (N + sig[p]) * M + (h + mv0[p]) % M))
        E.append((p * M + h, (N + sig[p]) * M + (h + mv1[p]) % M))
nv = 2 * N * M
hubid = {}
for i, p in enumerate(free):
    nh = 3 if i in FD else 2
    for side, base in (('A', p), ('B', N + sig[p])):
        for t in range(nh):
            hubid[side, 3 * i + t] = nv
            for h in range(M): E.append((nv, base * M + h))
            nv += 1
skipped = 0
for e in range(0, len(hg), 2):
    a, b = hg[e], hg[e + 1]
    if ('A', a) not in hubid or ('B', b) not in hubid: skipped += 1; continue
    E.append((hubid['A', a], hubid['B', b]))
with open(out, 'w') as f:
    f.write('%d\n' % nv)
    for u, v in E: f.write('%d %d\n' % (u, v))
print('n', nv, 'edges', len(E), 'hub edges skipped (disabled hubs)', skipped)
