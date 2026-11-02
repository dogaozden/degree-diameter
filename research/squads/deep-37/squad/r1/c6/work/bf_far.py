import sys, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/deep-37/src')
import gutil
base, testout, maxreg, cur = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
n, E, adj = gutil.load(base)
col = gutil.sides(adj)
Eset = set(tuple(sorted(e)) for e in E)
def far(edges):
    A = [[] for _ in range(n)]
    for a, b in edges: A[a].append(b); A[b].append(a)
    tot = 0
    for s in range(n):
        d = gutil.bfs(A, s)
        tot += n - len(d)
        tot += sum(1 for v in d if d[v] > 7)
    return tot // 2
lines = open(testout).read().split('\n')
res = []
for i, ln in enumerate(lines):
    if ln.startswith('REG'):
        S = [tuple(sorted(map(int, p.split('-')))) for p in ln.split()[2:]]
        L = lines[i+1].split()
        res.append((S, int(L[3]), int(L[1])))
ok = 0; bad = 0
for S, lnsmin, lnsleaves in res[:maxreg]:
    R = Eset - set(S)
    need = [3]*n
    for a, b in R: need[a] -= 1; need[b] -= 1
    defs = [v for v in range(n) if need[v] > 0]
    A_ = [v for v in defs if col[v] == 0]; B_ = [v for v in defs if col[v] == 1]
    P = [(a, b) for a in A_ for b in B_ if (min(a,b), max(a,b)) not in R]
    best = 10**9
    def rec(i, nd, chosen):
        global best
        if all(x == 0 for x in nd.values()):
            f = far(R | set(chosen))
            best = min(best, f); return
        if i == len(P): return
        a, b = P[i]
        if nd[a] > 0 and nd[b] > 0:
            nd[a] -= 1; nd[b] -= 1; chosen.append((min(a,b), max(a,b)))
            rec(i+1, nd, chosen)
            nd[a] += 1; nd[b] += 1; chosen.pop()
        rec(i+1, nd, chosen)
    rec(0, {v: need[v] for v in defs}, [])
    if best <= cur:
        good = (lnsmin == best)
    else:
        good = (lnsmin > cur)
    if good: ok += 1
    else: bad += 1; print("MISMATCH", S, "python min", best, "lns min", lnsmin)
print("regions", min(maxreg, len(res)), "ok", ok, "bad", bad)
