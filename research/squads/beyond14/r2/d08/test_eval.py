#!/usr/bin/env python3
# checks lift4 EVAL cost against exact python BFS count of (root, vertex) pairs at distance > D
import random, subprocess, sys, os
from collections import deque
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mklift import edges
def bfs(adj, s):
    d = {s: 0}; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in d: d[y] = d[x] + 1; q.append(y)
    return d
for (m, k, r, p) in [(7, 3, 2, 2), (13, 4, 5, 2), (13, 4, 5, 4), (7, 3, 2, 1)]:
    N = m * k
    rnd = random.Random(m * 100 + p)
    for trial in range(3):
        E = []
        for mm in range(4):
            pm = list(range(p)); rnd.shuffle(pm)
            for i in range(p): E.append((i, p + pm[i], rnd.randrange(N)))
        if len(set(E)) < len(E):
            continue
        fn = f"/tmp_test_{m}_{p}_{trial}.sol"
        fn = os.path.join(os.environ.get("TMPDIR", "/tmp/claude-0/-home-user-degree-diameter/05f92099-9dfa-5570-acc3-eed8240defa2/scratchpad"), f"t_{m}_{p}_{trial}.sol")
        with open(fn, "w") as f:
            f.write(f"{m} {k} {r} {p} 0\n" + "".join(f"{a} {b} {c}\n" for a, b, c in E))
        n, ed = edges(m, k, r, p, E)
        adj = [[] for _ in range(n)]
        for u, v in ed: adj[u].append(v); adj[v].append(u)
        assert all(len(a) == 4 for a in adj), "not 4-regular"
        roots = [u * N for u in range(2 * p)]
        dist = {x: bfs(adj, x) for x in roots}
        for D in (2, 3, 4, 5):
            exact = sum(1 for x in roots for y in range(n) if dist[x].get(y, 10**9) > D)
            env = dict(os.environ, D=str(D))
            out = subprocess.run(["./lift4", str(p), str(m), str(k), str(r), "1", "1", "/dev/null"], env=dict(env, EVAL=fn), capture_output=True, text=True).stdout
            got = int(out.split()[-1])
            print(m, k, p, trial, "D", D, "python", exact, "lift4", got, "OK" if exact == got else "MISMATCH")
