#!/usr/bin/env python3
"""Cubic bipartite controllers for the F_3^4 route-chart lift (hunt-d5). ctrl_sq.py m seconds seed OUT.edges [mode]
Needs: same-side distance <= 4 for every pair, every vertex on a 4-cycle. mode "sq": vertices partitioned into m/2
squares (K_{2,2}); the third edge of each vertex is an A-B perfect matching between squares (annealed by swaps).
mode "gen": any cubic bipartite graph (annealed by double edge swaps). Cost = far same-side pairs + 3 * (vertices on no
4-cycle). Writes the best graph ("2m" then "u v", A = 0..m-1, B = m..2m-1) when cost 0."""
import random, sys, time, math
def evaluate(m, adj):
    n = 2 * m; far = 0
    for s in range(n):
        dist = [-1] * n; dist[s] = 0; q = [s]; i = 0
        while i < len(q):
            x = q[i]; i += 1
            if dist[x] >= 4: continue
            for y in adj[x]:
                if dist[y] < 0: dist[y] = dist[x] + 1; q.append(y)
        side = 0 if s < m else m
        for t in range(side, side + m):
            if dist[t] < 0: far += 1
    no4 = 0
    for x in range(n):
        ok = False
        for a in adj[x]:
            for b in adj[x]:
                if a < b and len(set(adj[a]) & set(adj[b])) >= 2: ok = True
        if not ok: no4 += 1
    return far // 2 + 3 * no4
def main():
    m, secs, seed, out = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    mode = sys.argv[5] if len(sys.argv) > 5 else 'sq'
    random.seed(seed); n = 2 * m
    if mode == 'sq':
        assert m % 2 == 0
        sq = [(2 * i, 2 * i + 1, m + 2 * i, m + 2 * i + 1) for i in range(m // 2)]
        base = []
        for (a1, a2, b1, b2) in sq: base += [(a1, b1), (a1, b2), (a2, b1), (a2, b2)]
        perm = list(range(m))
        def build(p):
            ok = all(not (p[u] // 2 == u // 2) for u in range(m))
            adj = [[] for _ in range(n)]
            for (u, v) in base: adj[u].append(v); adj[v].append(u)
            for u in range(m): v = m + p[u]; adj[u].append(v); adj[v].append(u)
            return adj, ok
        random.shuffle(perm)
        adj, ok = build(perm); cur = evaluate(m, adj) + (0 if ok else 1000); best = cur; bestp = perm[:]
        t0 = time.time(); T = 2.0
        while time.time() - t0 < secs and best > 0:
            i, j = random.sample(range(m), 2); p2 = perm[:]; p2[i], p2[j] = p2[j], p2[i]
            adj2, ok2 = build(p2); c = evaluate(m, adj2) + (0 if ok2 else 1000)
            if c <= cur or random.random() < math.exp(-(c - cur) / T):
                perm, cur = p2, c
                if c < best: best, bestp = c, p2[:]; print(f"t={time.time()-t0:.1f} best={best}", file=sys.stderr)
            T = max(0.05, T * 0.9995)
        adj, _ = build(bestp)
    else:
        raise SystemExit("gen mode not written")
    print(f"RESULT ctrl m={m} mode={mode} best={best}")
    if best == 0:
        with open(out, 'w') as f:
            f.write(f"{n}\n")
            for u in range(m):
                for v in adj[u]: f.write(f"{u} {v}\n")
main()
