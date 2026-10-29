"""Tests of apsp_fast.c against research/lifts/coordinator_check/apsp_mt.c and against a plain BFS.
(1) Eight small graphs (incidence graphs of PG(2,7), PG(2,23), PG(2,31), PG(2,31) minus one incidence, random
bipartite graphs with pendant paths, a non-bipartite and a disconnected graph): the output of apsp_fast (several
builds) must equal that of apsp_mt line for line. (2) A random graph with eccentricities 13..20: the diameter printed
for each of 335 source ranges must equal the largest BFS eccentricity in the range.
Usage: python3 test_apsp_fast.py APSP_MT APSP_FAST [MORE_APSP_FAST_BUILDS...]   (run in an empty directory)"""
import random
import subprocess
import sys
from collections import deque

mt, fasts = sys.argv[1], sys.argv[2:]


def pg(q):
    pts = [(x, y, 1) for x in range(q) for y in range(q)] + [(x, 1, 0) for x in range(q)] + [(1, 0, 0)]
    N = len(pts)
    return 2 * N, [(i, N + j) for j, L in enumerate(pts) for i, p in enumerate(pts)
                   if sum(a * b for a, b in zip(p, L)) % q == 0]


def write(fn, n, E):
    with open(fn, 'w') as f:
        f.write(f'{n}\n' + '\n'.join(f'{a} {b}' for a, b in E) + '\n')


rng = random.Random(5)


def randbip(h, k, path=0, where=0):
    E = set()
    for t in range(k):
        perm = list(range(h)); rng.shuffle(perm)
        E |= {(i, h + perm[i]) for i in range(h)}
    E = sorted(E); n = 2 * h; v = where
    for s in range(path):
        E.append((v, n)); v = n; n += 1
    return n, E


graphs = {}
for q in (7, 23, 31):
    graphs[f'pg{q}'] = pg(q)
n, E = pg(31); graphs['pg31minus'] = (n, E[1:])
graphs['rb3'] = randbip(1500, 3)
graphs['rb4path'] = randbip(2600, 4, 3, 17)
n, E = randbip(2600, 4); graphs['nonbip'] = (n, E + [(0, 1)])
n, E = randbip(700, 3); graphs['disc'] = (n, [e for e in E if 5 not in e])
fails = 0
for name, (n, E) in graphs.items():
    write(name + '.edges', n, E)
    ref = subprocess.run([mt, name + '.edges', '40', '3', '1'], capture_output=True, text=True).stdout
    for b in fasts:
        out = subprocess.run([b, name + '.edges', '40', '3', '3'], capture_output=True, text=True).stdout
        out = out.replace(f' sources=0..{n}', '')
        if out != ref:
            fails += 1; print('DIFF', name, b, repr(out), repr(ref))
    print(name, ref.split('\n')[0])

rng = random.Random(11)
n, E = randbip(900, 3)
for start, length in ((5, 4), (700, 6), (1500, 2)):
    v = start
    for s in range(length):
        E.append((v, n)); v = n; n += 1
write('ecc.edges', n, E)
adj = [[] for _ in range(n)]
for a, b in E:
    adj[a].append(b); adj[b].append(a)


def ecc(s):
    d = [-1] * n; d[s] = 0; Q = deque([s])
    while Q:
        x = Q.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1; Q.append(y)
    return max(d)


ecc_ = [ecc(s) for s in range(n)]
ranges = [(k, k + 1) for k in range(0, n, 7)] + [(k, min(n, k + L)) for L in (37, 256, 300, 513) for k in range(0, n, 97)]
for lo, hi in ranges:
    for b in fasts:
        out = subprocess.run([b, 'ecc.edges', '40', '3', '2', str(lo), str(hi)], capture_output=True, text=True).stdout
        if int(out.split('diameter=')[1].split()[0]) != max(ecc_[lo:hi]):
            fails += 1; print('DIFF ecc', b, lo, hi)
print(f'eccentricities {min(ecc_)}..{max(ecc_)}, {len(ranges)} ranges x {len(fasts)} builds; failures: {fails}')
