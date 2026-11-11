# g11: write base graphs as edge files "V E" + "a b" lines (a<b), and verify regularity, bipartiteness, girth.
import os, sys, itertools
from collections import deque
OUT = "/home/user/degree-diameter/research/squads/beyond13/r4/g11/bases"
SRC = "/home/user/degree-diameter/research/frontier/beyond13/lifts/bases"

def read_base(path):
    with open(path) as f:
        toks = f.read().split()
    V = int(toks[0]); nums = list(map(int, toks[1:]))
    edges = set()
    for i in range(0, len(nums), 2):
        a, b = nums[i], nums[i+1]
        edges.add((min(a, b), max(a, b)))
    return V, sorted(edges)

def tutte8():
    n = 30; sh = [-13, -9, 7, -7, 9, 13] * 5
    edges = set()
    for i in range(n):
        edges.add(tuple(sorted((i, (i+1) % n))))
        edges.add(tuple(sorted((i, (i+sh[i]) % n))))
    return n, sorted(edges)

def gf3_points(k):
    pts = []
    for v in itertools.product(range(3), repeat=k):
        if any(v):
            # normalise: first nonzero coordinate = 1
            i = next(j for j in range(k) if v[j])
            if v[i] == 1:
                pts.append(v)
    return pts

def pg23():
    P = gf3_points(3); L = gf3_points(3)
    idx = {p: i for i, p in enumerate(P)}
    edges = []
    for j, l in enumerate(L):
        for i, p in enumerate(P):
            if sum(a*b for a, b in zip(p, l)) % 3 == 0:
                edges.append((i, len(P)+j))
    return 2*len(P), sorted(edges)

def gq33():
    P = gf3_points(4)
    def B(x, y):  # symplectic form
        return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % 3
    def norm(v):
        i = next(j for j in range(4) if v[j]); inv = 1 if v[i] == 1 else 2
        return tuple((inv*a) % 3 for a in v)
    pidx = {p: i for i, p in enumerate(P)}
    lines = set()
    for p, q in itertools.combinations(P, 2):
        if B(p, q) == 0:
            pts = set()
            for a, b in itertools.product(range(3), repeat=2):
                if a or b:
                    v = tuple((a*x + b*y) % 3 for x, y in zip(p, q))
                    pts.add(pidx[norm(v)])
            lines.add(frozenset(pts))
    lines = sorted(sorted(l) for l in lines)
    edges = []
    for j, l in enumerate(lines):
        for i in l:
            edges.append((i, len(P)+j))
    return 2*len(P), sorted(edges), len(lines)

def check(V, edges):
    adj = [[] for _ in range(V)]
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    degs = set(len(x) for x in adj)
    # bipartite
    col = [-1]*V; col[0] = 0; dq = deque([0]); bip = True
    while dq:
        v = dq.popleft()
        for w in adj[v]:
            if col[w] < 0: col[w] = 1-col[v]; dq.append(w)
            elif col[w] == col[v]: bip = False
    # girth
    girth = 10**9
    for s in range(V):
        dist = [-1]*V; par = [-1]*V; dist[s] = 0; dq = deque([s])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dist[v]+1; par[w] = v; dq.append(w)
                elif par[v] != w:
                    girth = min(girth, dist[v]+dist[w]+1)
    conn = all(d >= 0 for d in dist)
    return degs, bip, girth, conn

if __name__ == "__main__":
    bases = {}
    for fn in sorted(os.listdir(SRC)):
        if fn.endswith(".txt"):
            bases[fn[:-4]] = read_base(os.path.join(SRC, fn))
    bases["tutte8"] = tutte8()
    bases["pg23_levi"] = pg23()
    V, e, nl = gq33()
    bases["gq33_levi"] = (V, e)
    print("gq33 lines:", nl)
    os.makedirs(OUT, exist_ok=True)
    for name, (V, e) in bases.items():
        degs, bip, girth, conn = check(V, e)
        if degs in ({3}, {4}) and bip and conn:
            with open(os.path.join(OUT, name + ".edges"), "w") as f:
                f.write(f"{V} {len(e)}\n")
                for a, b in e: f.write(f"{a} {b}\n")
        print(f"{name:12s} V={V:3d} E={len(e):4d} degs={sorted(degs)} bip={bip} girth={girth} conn={conn}")
