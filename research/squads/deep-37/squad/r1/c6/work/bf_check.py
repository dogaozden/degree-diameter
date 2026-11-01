import sys, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/deep-37/src')
import gutil
base = sys.argv[1]; testout = sys.argv[2]; maxreg = int(sys.argv[3])
n, E, adj = gutil.load(base)
col = gutil.sides(adj)
Eset = set(tuple(sorted(e)) for e in E)
regs = []
lines = open(testout).read().split('\n')
for i, ln in enumerate(lines):
    if ln.startswith('REG'):
        parts = ln.split()[2:]
        S = [tuple(sorted(map(int, p.split('-')))) for p in parts]
        leaves = int(lines[i+1].split()[1])
        regs.append((S, leaves))
bad = 0
for S, leaves in regs[:maxreg]:
    Rset = Eset - set(S)
    need = [3]*n
    for a, b in Rset: need[a] -= 1; need[b] -= 1
    radj = set(Rset)
    defs = [v for v in range(n) if need[v] > 0]
    P = [(a, b) for a in defs for b in defs if col[a] == 0 and col[b] == 1 and (min(a,b), max(a,b)) not in radj] if False else []
    A = [v for v in defs if col[v] == 0]; B = [v for v in defs if col[v] == 1]
    P = [(a, b) for a in A for b in B if (min(a,b), max(a,b)) not in radj]
    cnt = 0
    def rec(i, nd):
        global cnt
        if all(x == 0 for x in nd.values()):
            cnt += 1; return
        if i == len(P): return
        a, b = P[i]
        if nd[a] > 0 and nd[b] > 0:
            nd[a] -= 1; nd[b] -= 1; rec(i+1, nd); nd[a] += 1; nd[b] += 1
        rec(i+1, nd)
    nd = {v: need[v] for v in defs}
    cnt = 0
    rec(0, nd)
    if cnt != leaves:
        bad += 1; print("MISMATCH", S, "brute", cnt, "lns", leaves)
print("checked", min(maxreg, len(regs)), "regions; mismatches", bad)
