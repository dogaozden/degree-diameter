# find_aut.py: random automorphisms of the H(3) incidence graph by distance-preserving backtracking.
# usage: find_aut.py SEED TRIES -> appends fixed-point-free automorphisms of prime order 13 (or 7) to auts_<p>.txt
import sys, random
from collections import deque
from math import gcd
random.seed(int(sys.argv[1])); TRIES = int(sys.argv[2])
sys.setrecursionlimit(10000)
E = [tuple(map(int, l.split())) for l in open('base.txt').read().split('\n')[1:] if l.strip()]
N = 728
adj = [[] for _ in range(N)]
for u, v in E:
    adj[u].append(v); adj[v].append(u)
D = []
for s in range(N):
    d = [-1] * N; d[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1; q.append(y)
    D.append(d)
def bfs_tree(r):
    seen = [False]*N; seen[r] = True; order = [r]; par = [-1]*N; q = deque([r])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if not seen[y]:
                seen[y] = True; par[y] = x; order.append(y); q.append(y)
    return order, par
def random_aut(r0, t0, budget=200000):
    order, par = bfs_tree(r0)
    img = [-1]*N; used = [False]*N
    img[r0] = t0; used[t0] = True
    assigned = [r0]; nodes = [0]
    def rec(i):
        nodes[0] += 1
        if nodes[0] > budget: return False
        if i == N: return True
        v = order[i]
        cands = [c for c in adj[img[par[v]]] if not used[c]]
        random.shuffle(cands)
        for c in cands:
            if any(D[v][w] != D[c][img[w]] for w in assigned): continue
            img[v] = c; used[c] = True; assigned.append(v)
            if rec(i+1): return True
            assigned.pop(); used[c] = False; img[v] = -1
        return False
    return img if rec(1) else None
def order_of(p):
    seen = [False]*N; o = 1
    for s in range(N):
        if seen[s]: continue
        L = 0; x = s
        while not seen[x]:
            seen[x] = True; x = p[x]; L += 1
        o = o*L//gcd(o, L)
    return o
found = {}
for t in range(TRIES):
    r0 = random.randrange(N); t0 = random.randrange(N)
    img = random_aut(r0, t0)
    if img is None: continue
    o = order_of(img)
    found[o] = found.get(o, 0) + 1
    for p in (13, 7):
        if o % p:
            continue
        pw = list(range(N))
        for _ in range(o // p): pw = [img[x] for x in pw]
        fp = sum(1 for x in range(N) if pw[x] == x)
        print("try", t, "order", o, "prime", p, "fixed pts", fp, "side swap", (r0 < 364) != (t0 < 364), flush=True)
        if fp == 0:
            with open('auts_%d.txt' % p, 'a') as f:
                f.write(' '.join(map(str, pw)) + '\n')
print("orders seen", sorted(found.items()), flush=True)
