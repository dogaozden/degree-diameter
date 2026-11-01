"""Brute force: all G-invariant cubic bipartite graphs on a G-set (group file), connected, with bipartite
diameter <= D; prints iso-class certificates count. For validating orbdfs on small cases."""
import sys, subprocess, collections
sys.path.insert(0, __file__.rsplit('/',1)[0]); from iso import g6
def readgroup(fn):
    t = open(fn).read().split(); n, ng = int(t[0]), int(t[1]); P = []; k = 2
    for g in range(ng): P.append([int(x) for x in t[k:k+n]]); k += n
    col = [int(x) for x in t[k:k+n]]; return n, P, col
n, P, col = readgroup(sys.argv[1]); D = int(sys.argv[2])
# edge orbits on A x B
seen = {}; orbs = []
for a in range(n):
    for b in range(n):
        if col[a] == 0 and col[b] == 1 and (a, b) not in seen:
            o = set()
            for p in P:
                x, y = p[a], p[b]
                if col[x] == 1: x, y = y, x
                o.add((x, y))
            for e in o: seen[e] = len(orbs)
            orbs.append(sorted(o))
inc = []
for o in orbs:
    c = collections.Counter()
    for x, y in o: c[x] += 1; c[y] += 1
    inc.append(c)
sols = []
deg = [0]*n
def rec(i, chosen):
    if i == len(orbs):
        if all(d == 3 for d in deg): sols.append(list(chosen))
        return
    # prune: vertex whose all orbits decided
    rec(i+1, chosen)
    c = inc[i]
    if all(deg[v] + k <= 3 for v, k in c.items()):
        for v, k in c.items(): deg[v] += k
        chosen.append(i); 
        # feasibility: no vertex can exceed; quick check of remaining capacity skipped
        rec(i+1, chosen); chosen.pop()
        for v, k in c.items(): deg[v] -= k
sys.setrecursionlimit(10000)
rec(0, [])
good = []
for s in sols:
    adj = [[] for _ in range(n)]
    for i in s:
        for x, y in orbs[i]: adj[x].append(y); adj[y].append(x)
    # connected + diameter
    ok = True; diam = 0
    for src in range(n):
        d = {src: 0}; q = [src]
        for u in q:
            for w in adj[u]:
                if w not in d: d[w] = d[u] + 1; q.append(w)
        if len(d) < n: ok = False; break
        diam = max(diam, max(d.values()))
    if ok and diam <= D: good.append(g6(n, adj))
r = subprocess.run(["nauty-labelg", "-q"], input="\n".join(good) + "\n", capture_output=True, text=True)
cs = set(r.stdout.split()) if good else set()
print("edge orbits", len(orbs), "invariant cubic", len(sols), "connected diam<=D", len(good), "iso classes", len(cs))
open(sys.argv[3], "w").write("\n".join(sorted(cs)) + "\n")
