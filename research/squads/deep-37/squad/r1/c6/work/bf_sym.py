import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/deep-37/src')
import gutil
base, testout, grpf, maxreg = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
n, E, adj = gutil.load(base)
col = gutil.sides(adj)
t = open(grpf).read().split('\n')
nn, order = map(int, t[0].split())
G = [list(map(int, t[1+i].split())) for i in range(order)]
Eset = set(tuple(sorted(e)) for e in E)
lines = open(testout).read().split('\n')
regs = []
for i, ln in enumerate(lines):
    if ln.startswith('REG'):
        S = [tuple(sorted(map(int, p.split('-')))) for p in ln.split()[2:]]
        regs.append((S, int(lines[i+1].split()[1])))
bad = 0
for S, leaves in regs[:maxreg]:
    R = Eset - set(S)
    need = [3]*n
    for a, b in R: need[a] -= 1; need[b] -= 1
    radj = set(R)
    # all pair-orbits under G (pairs of opposite colour, not in R)
    seen = set(); orbs = []
    for a in range(n):
        for b in range(n):
            if a == b or col[a] == col[b]: continue
            p = (min(a,b), max(a,b))
            if p in seen or p in radj: continue
            if need[a] <= 0 or need[b] <= 0: continue
            orb = set()
            for g in G:
                x, y = g[a], g[b]
                orb.add((min(x,y), max(x,y)))
            seen |= orb
            # validity: all pairs free, degrees within need
            ok = all(q not in radj for q in orb)
            if ok:
                cnt = {}
                for x, y in orb:
                    cnt[x] = cnt.get(x, 0) + 1; cnt[y] = cnt.get(y, 0) + 1
                ok = all(cnt[z] <= need[z] for z in cnt)
            if ok: orbs.append((sorted(orb), cnt))
    # DFS include/exclude over orbits
    rem = need[:]
    count = 0
    def rec(j):
        global count
        if j == len(orbs):
            if all(x == 0 for x in rem): count += 1
            return
        # prune: vertices with rem>0 that have no remaining orbit: skip check for simplicity
        orb, cnt = orbs[j]
        if all(rem[z] >= c for z, c in cnt.items()):
            for z, c in cnt.items(): rem[z] -= c
            rec(j+1)
            for z, c in cnt.items(): rem[z] += c
        rec(j+1)
    rec(0)
    if count != leaves:
        bad += 1; print("MISMATCH", len(S), "brute", count, "lns", leaves)
print("checked", min(maxreg, len(regs)), "regions; mismatches", bad, "orbs last", len(orbs))
