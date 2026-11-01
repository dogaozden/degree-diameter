# find_aut2.py SEED TRIES: random automorphisms of the H(3) incidence graph, pinned on a random apartment (12-cycle).
# Every 12-cycle is an apartment; an automorphism is fixed by the images of an apartment up to few choices.
# Saves fixed-point-free automorphisms of order 13 (and 7) to auts_<p>.txt; prints order statistics.
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
def apartment(r):
    """random 12-cycle through r: two different geodesics of length 6 from r to an opposite vertex u."""
    opp = [u for u in range(N) if D[r][u] == 6]
    u = random.choice(opp)
    # random geodesics from r to u: walk backwards from u choosing random predecessors
    def geo():
        path = [u]; x = u
        while x != r:
            cands = [y for y in adj[x] if D[r][y] == D[r][x] - 1]
            x = random.choice(cands); path.append(x)
        return path[::-1]  # r ... u
    p1 = geo()
    for _ in range(50):
        p2 = geo()
        if p2[1] != p1[1]:
            break
    else:
        return None
    cyc = p1 + p2[-2:0:-1]  # r..u then back along p2 (excluding endpoints) -> length 12
    assert len(cyc) == 12 and len(set(cyc)) == 12, cyc
    return cyc
def extend(a_src, a_dst, budget=20000):
    """map apartment a_src[i] -> a_dst[i]; extend to all vertices by distance-checked backtracking."""
    img = [-1]*N; used = [False]*N
    assigned = []
    for x, y in zip(a_src, a_dst):
        img[x] = y; used[y] = True; assigned.append(x)
    if any(D[x][w] != D[img[x]][img[w]] for x in a_src for w in a_src):
        return None
    # BFS order from the apartment
    order = []; par = [-1]*N; dist = [-1]*N
    q = deque()
    for x in a_src:
        dist[x] = 0; q.append(x)
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x]+1; par[y] = x; order.append(y); q.append(y)
    nodes = [0]
    def rec(i):
        nodes[0] += 1
        if nodes[0] > budget: return False
        if i == len(order): return True
        v = order[i]
        cands = [c for c in adj[img[par[v]]] if not used[c]]
        random.shuffle(cands)
        for c in cands:
            if any(D[v][w] != D[c][img[w]] for w in assigned): continue
            img[v] = c; used[c] = True; assigned.append(v)
            if rec(i+1): return True
            assigned.pop(); used[c] = False; img[v] = -1
        return False
    return img if rec(0) else None
def order_of(p):
    seen = [False]*N; o = 1
    for s in range(N):
        if seen[s]: continue
        L = 0; x = s
        while not seen[x]:
            seen[x] = True; x = p[x]; L += 1
        o = o*L//gcd(o, L)
    return o
stats = {}
for t in range(TRIES):
    r = random.randrange(N)
    A = apartment(r)
    if A is None: continue
    B = apartment(random.randrange(N))
    if B is None: continue
    for rot in range(12):
        for rev in (False, True):
            Bp = B[rot:] + B[:rot]
            if rev: Bp = Bp[::-1]
            # apartment alignment must respect sides for a side-preserving map; try all, the extension decides
            img = extend(A, Bp)
            if img is None: continue
            if any(v < 0 for v in img): continue
            # verify automorphism
            ok = all(((img[x] in adj[img[y]]) == (y in adj[x])) for x in range(N) for y in adj[x])
            if not ok: continue
            o = order_of(img)
            stats[o] = stats.get(o, 0) + 1
            for p in (13, 7):
                if o % p: continue
                pw = list(range(N))
                for _ in range(o // p): pw = [img[x] for x in pw]
                fp = sum(1 for x in range(N) if pw[x] == x)
                print("found order", o, "prime", p, "fixed", fp, flush=True)
                if fp == 0:
                    with open('auts_%d.txt' % p, 'a') as f:
                        f.write(' '.join(map(str, pw)) + '\n')
print("orders", sorted(stats.items()), flush=True)
