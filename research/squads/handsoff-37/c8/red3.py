#!/usr/bin/env python3
# Random large move: from conder168 remove two vertex pairs (random adjacent a-b, reconnect the 4 outer neighbours),
# n = 164, then insert three pairs greedily (insbest, exhaustive best 2-edge insertion each time), n = 170.
import random, subprocess, sys, os
seed0, trials = int(sys.argv[1]), int(sys.argv[2])
def colour(n, adj):
    col = [-1]*n; col[0] = 0; q = [0]
    for x in q:
        for y in adj[x]:
            if col[y] < 0: col[y] = 1 - col[x]; q.append(y)
    return col
def reduce_once(n, E, rng):
    adj = [set() for _ in range(n)]
    for a, b in E: adj[a].add(b); adj[b].add(a)
    col = colour(n, adj)
    while True:
        a, b = rng.choice(E)
        if col[a] != 0: a, b = b, a
        a1, a2 = sorted(adj[a] - {b}); b1, b2 = sorted(adj[b] - {a})
        opts = [((a1, b1), (a2, b2)), ((a1, b2), (a2, b1))]
        rng.shuffle(opts)
        for (p, q), (r, s) in opts:
            if q in adj[p] or s in adj[r]: continue
            keep = [v for v in range(n) if v not in (a, b)]
            idx = {v: i for i, v in enumerate(keep)}
            NE = [(idx[u], idx[v]) for u, v in E if a not in (u, v) and b not in (u, v)]
            NE += [(idx[p], idx[q]), (idx[r], idx[s])]
            return n - 2, NE
def write(fn, nn, edges):
    with open(fn, 'w') as f:
        f.write(f"{nn}\n"); [f.write(f"{u} {v}\n") for u, v in edges]
L = open('../shared/seeds/conder168.edges').read().split(); n0 = int(L[0])
E0 = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
best = 10**9; hist = {}
for t in range(trials):
    rng = random.Random(seed0 * 100000 + t)
    n, E = n0, E0
    for _ in range(2): n, E = reduce_once(n, E, rng)
    fn = f"out/r3_{seed0}.edges"
    write(fn, n, E)
    for k in range(3):
        f2 = f"out/r3_{seed0}_{k}.edges"
        subprocess.run(['./insbest', fn, f2], capture_output=True, text=True)
        fn = f2
    far = int(subprocess.run(['../bin/score37', fn], capture_output=True, text=True).stdout.split('far=')[1].split()[0])
    hist[far] = hist.get(far, 0) + 1
    if far < best:
        best = far; os.system(f"cp {fn} out/r3_best_{seed0}.edges")
    print(f"trial {t} far170={far}", flush=True)
print("BEST", best, "hist", sorted(hist.items())[:10], flush=True)
