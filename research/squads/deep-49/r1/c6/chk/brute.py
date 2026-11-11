# Independent check of bicm: bi-coset graphs built from group cosets directly, all zeta-invariant 4-sets (no normal form).
import sys
from collections import deque
m, kp, h, r = map(int, sys.argv[1:5]); DD = int(sys.argv[5]) if len(sys.argv) > 5 else 9
k = h * kp
assert pow(r, k, m) == 1 % m
def mul(x, y):
    a, j = x; b, l = y
    return ((a + pow(r, j, m) * b) % m, (j + l) % k)
G = [(a, j) for a in range(m) for j in range(k)]
Hs = [(0, kp * t % k) for t in range(h)]           # H = <(0,kp)>, order h
def cos_of(x): return frozenset(mul(x, hh) for hh in Hs)   # right coset xH
cos = sorted({cos_of(x) for x in G}, key=lambda c: sorted(c))
cidx = {}
for i, c in enumerate(cos):
    for x in c: cidx[x] = i
nc = len(cos)
zeta = pow(r, kp, m)
pairs = [(u, v) for u in range(m) for v in range(kp)]
seen = set(); orbits = []
for p in pairs:
    if p in seen: continue
    o = []; q = p
    while q not in seen:
        seen.add(q); o.append(q); q = ((zeta * q[0]) % m, q[1])
    orbits.append(tuple(o))
def graph(N0):
    # A-coset C ~ B-coset cos_of(x s) for s in N0; check the neighbourhood is independent of representative x
    nbA = []
    for c in cos:
        nb_ref = None
        for x in sorted(c):
            nb = frozenset(cidx[mul(x, s)] for s in N0)
            if nb_ref is None: nb_ref = nb
            elif nb != nb_ref: return None   # not well defined
        nbA.append(sorted(nb_ref))
    nbB = [[] for _ in range(nc)]
    for a, nb in enumerate(nbA):
        for b in nb: nbB[b].append(a)
    return nbA, nbB
def bfs(side, src, nbA, nbB, D=DD):
    # vertices: ('A',i) and ('B',i); returns number of unreached-within-D vertices
    dist = {(side, src): 0}; q = deque([(side, src)])
    while q:
        t, i = q.popleft()
        d = dist[(t, i)]
        if d >= D: continue
        nbrs = [('B', b) for b in nbA[i]] if t == 'A' else [('A', a) for a in nbB[i]]
        for y in nbrs:
            if y not in dist:
                dist[y] = d + 1; q.append(y)
    return 2 * nc - len(dist)
best = None; cnt = 0; bestset = None
ids = [i for i, c in enumerate(cos) if (0, 0) in c]
root = ids[0]
for sz in range(0, 5):
    pass
def subsets_orbits(target):
    # all unions of distinct orbits with total size target
    res = []
    def rec(i, cur, tot):
        if tot == target: res.append(list(cur)); return
        if i >= len(orbits) or tot > target: return
        if tot + len(orbits[i]) <= target:
            cur.append(i); rec(i + 1, cur, tot + len(orbits[i])); cur.pop()
        rec(i + 1, cur, tot)
    rec(0, [], 0)
    return res
for combo in subsets_orbits(4):
    N0 = [p for i in combo for p in orbits[i]]
    g = graph(N0)
    if g is None:
        raise SystemExit("ill-defined neighbourhood")
    nbA, nbB = g
    # A-root and B-root (the coset of identity on each side)
    tot = bfs('A', root, nbA, nbB) + bfs('B', root, nbA, nbB)
    cnt += 1
    if best is None or tot < best: best = tot; bestset = N0; nties = 1
    elif tot == best: nties += 1
print("brute m", m, "kp", kp, "h", h, "r", r, "zeta", zeta, "sets", cnt, "best two-root far", best, "ties", nties, "N0", bestset)
