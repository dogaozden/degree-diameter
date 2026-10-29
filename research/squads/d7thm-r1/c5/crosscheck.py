"""Independent cross-check of bfs.c with a pure-Python BFS, plus a PG(2,s) plane property test."""
import sys, collections, random
sys.argv = [sys.argv[0], "11"]
import hubcheck as H

def py_bfs_stats(g, sameT=6, diffT=5):
    adj = [[] for _ in range(g.n)]
    for u, v in g.edges:
        adj[u].append(v); adj[v].append(u)
    maxsame = maxdiff = sameviol = diffviol = 0
    for s in range(g.n):
        dist = [-1] * g.n; dist[s] = 0; dq = collections.deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1; dq.append(y)
        for t in range(g.n):
            if t == s: continue
            d = dist[t]
            if g.col[t] == g.col[s]:
                if d < 0 or d > sameT: sameviol += 1
                if d >= 0: maxsame = max(maxsame, d)
            else:
                if d < 0 or d > diffT: diffviol += 1
                if d >= 0: maxdiff = max(maxdiff, d)
    return maxsame, sameviol, maxdiff, diffviol

r = random.Random(3)
bases = {2: H.load_hex(2), 3: H.load_hex(3)}
tests = []
tests.append(("H(2) base", bases[2]))
g, _ = H.blowup(bases[2], 3, r); tests.append(("blowup H(2) c=3", g))
g, n = H.pg2(4); tests.append(("PG(2,4)", g))
g, _, _ = H.pendant_plane(3, 2, 2, 20, 9, 15, 10, r); tests.append(("C s=3", g))
g, _, _ = H.pendant_plane(3, 1, 3, 13, 0, 0, 0, r); tests.append(("C s=3 small", g))
for name, g in tests:
    c = H.bfs_check(g, 6, 5)
    ms, sv, md, dv = py_bfs_stats(g, 6, 5)
    agree = (ms, sv, md, dv) == (c["maxsame"], c["sameviol"], c["maxdiff"], c["diffviol"])
    print(f"{name}: n={g.n} C=({c['maxsame']},{c['sameviol']},{c['maxdiff']},{c['diffviol']}) "
          f"PY=({ms},{sv},{md},{dv}) agree={agree}")

# PG(2,s): every pair of points on exactly one common line, every line has s+1 points
for s in (2, 3, 4, 5):
    g, n = H.pg2(s)
    pts = range(n)
    lines = collections.defaultdict(set)
    for u, v in g.edges:
        p, l = (u, v) if u < n else (v, u)
        lines[l].add(p)
    common = collections.Counter()
    for l, S in lines.items():
        for a in S:
            for b in S:
                if a < b: common[(a, b)] += 1
    ok = len(lines) == n and all(len(S) == s + 1 for S in lines.values()) and \
         len(common) == n * (n - 1) // 2 and all(v == 1 for v in common.values())
    print(f"PG(2,{s}) plane check (n={n}, lines={len(lines)}): {ok}")
