#!/usr/bin/env python3
# prep.py KIND (pts|lines): builds the h-quotient of the orbit graph og_KIND.txt.
# Writes P_KIND.txt (permutation of orbit-graph vertices induced by h) and q_KIND.txt (quotient graph:
# "NQ EQ", then per quotient vertex "w k members... d nbrs..."; w = 3 for a 3-cycle of P, 1 for a P-fixed vertex).
import sys, numpy as np
kind = sys.argv[1]
BASE = '/home/user/degree-diameter/research/squads/d16D7_r2/'
g = np.fromfile(BASE + f'data/g13o61_{kind}.bin', dtype='<i4').astype(np.int64)
h = np.fromfile(BASE + f'data/g13o183_{kind}.bin', dtype='<i4').astype(np.int64)
N = len(g)
gp = g.tolist()
omin = [0] * N
seen = bytearray(N)
for s in range(N):
    if seen[s]: continue
    cyc = []; x = s
    while not seen[x]:
        seen[x] = 1; cyc.append(x); x = gp[x]
    m = min(cyc)
    for y in cyc: omin[y] = m
omin = np.array(omin, dtype=np.int64)
lines = open(BASE + f'og_{kind}.txt')
M, E = map(int, next(lines).split())
rep = np.full(M, -1, dtype=np.int64)
nb = [None] * M
for line in lines:
    a = line.split()
    if not a: continue
    idx, r, d = int(a[0]), int(a[1]), int(a[2])
    rep[idx] = r; nb[idx] = list(map(int, a[3:3 + d]))
assert (rep >= 0).all()
print('M', M, 'E', E, 'sum deg/2', sum(len(x) for x in nb) // 2)
assert all(len(set(nb[v])) == len(nb[v]) for v in range(M))
print('rep is orbit min for all vertices:', bool(np.all(omin[rep] == rep)))
# symmetric adjacency
adjset = [set(x) for x in nb]
assert all(v in adjset[u] for u in range(M) for v in nb[u]), 'asymmetric'
vmin = np.full(N, -1, dtype=np.int64)
vmin[rep] = np.arange(M)
# P: vertex of the g-orbit containing h(rep)
P = np.empty(M, dtype=np.int64)
for v in range(M):
    x = h[rep[v]]
    P[v] = vmin[omin[x]]
assert (P >= 0).all(), 'h maps a vertex orbit outside the vertex set'
assert len(set(P.tolist())) == M, 'P not a bijection'
P3 = P[P[P]]
print('P^3 = id:', bool(np.all(P3 == np.arange(M))))
print('fixed vertices of P:', int(np.sum(P == np.arange(M))))
ok = all(int(P[u]) in adjset[int(P[v])] for v in range(M) for u in nb[v])
print('P maps edges to edges:', ok)
with open(BASE + f'c5/P_{kind}.txt', 'w') as f:
    f.write('\n'.join(map(str, P.tolist())) + '\n')
# P-cycles
cyc_of = np.full(M, -1, dtype=np.int64)
cycles = []
for v in range(M):
    if cyc_of[v] >= 0: continue
    c = [v]; cyc_of[v] = len(cycles); x = int(P[v])
    while x != v:
        c.append(x); cyc_of[x] = len(cycles); x = int(P[x])
    cycles.append(c)
hist = {}
for c in cycles: hist[len(c)] = hist.get(len(c), 0) + 1
print('P-cycle histogram', hist)
keep = []
for ci, c in enumerate(cycles):
    if len(c) == 1:
        keep.append(ci)
    elif len(c) == 3 and not any(u in adjset[w] for u in c for w in c if u != w):
        keep.append(ci)
print('kept cycles', len(keep), 'weight3', sum(1 for ci in keep if len(cycles[ci]) == 3),
      'weight1', sum(1 for ci in keep if len(cycles[ci]) == 1))
qidx = {ci: i for i, ci in enumerate(keep)}
qadj = [set() for _ in keep]
for u in range(M):
    if cyc_of[u] not in qidx: continue
    for v in nb[u]:
        if cyc_of[v] in qidx and cyc_of[v] != cyc_of[u]:
            qadj[qidx[cyc_of[u]]].add(qidx[cyc_of[v]])
NQ = len(keep)
EQ = sum(len(a) for a in qadj) // 2
print('quotient NQ', NQ, 'EQ', EQ, 'avg deg', 2 * EQ / max(NQ, 1))
with open(BASE + f'c5/q_{kind}.txt', 'w') as f:
    f.write(f'{NQ} {EQ}\n')
    for i, ci in enumerate(keep):
        c = cycles[ci]
        f.write('%d %d %s %d %s\n' % (3 if len(c) == 3 else 1, len(c), ' '.join(map(str, c)),
                                      len(qadj[i]), ' '.join(map(str, sorted(qadj[i])))))
