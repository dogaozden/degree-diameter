# c6_analyze.py FLAGS GHFILE : independent check (BFS distances in the incidence graph, zones from the definitions)
# and structure summary of a packing: pairwise distances of freed points / lines, and pointing conditions.
import sys, collections, itertools
flagsfile, ghfile = sys.argv[1], sys.argv[2]
with open(ghfile) as f:
    P, q = map(int, f.readline().split())
    lines = [list(map(int, f.readline().split())) for _ in range(P)]
# lines[l] = q+1 points; points on lines
pl = collections.defaultdict(list)
for l, pts in enumerate(lines):
    assert len(pts) == q + 1
    for p in pts: pl[p].append(l)
assert all(len(pl[p]) == q + 1 for p in range(P))
flags = [tuple(map(int, s.split())) for s in open(flagsfile) if s.strip()]
assert len(set(p for p, _ in flags)) == len(flags), "points not distinct"
for p, l in flags: assert l in pl[p], "not incident"
# zones from the definitions: point zone = {p} U {points collinear with p, not on l}; line zone = {l} U {lines meeting l at x != p}
def zone_pts(p, l):
    Z = {p}
    for L in pl[p]:
        if L != l:
            Z |= set(x for x in lines[L] if x != p) - set(lines[l])
    return Z
def zone_lines(p, l):
    Z = {l}
    for x in lines[l]:
        if x != p:
            Z |= set(K for K in pl[x] if K != l)
    return Z
ZP = [zone_pts(p, l) for p, l in flags]; ZL = [zone_lines(p, l) for p, l in flags]
assert all(len(z) == q * q + 1 for z in ZP) and all(len(z) == q * q + 1 for z in ZL)
bad = [(i, j) for i, j in itertools.combinations(range(len(flags)), 2) if ZP[i] & ZP[j] or ZL[i] & ZL[j]]
print("flags", len(flags), "zone-overlapping pairs", len(bad), "VALID" if not bad else "INVALID")
# point-graph distance (incidence distance) between points
def inc_dist(a, b):
    if a == b: return 0
    seen = {a: 0}; frontier = [('p', a)]
    dist_p = {a: 0}; dist_l = {}
    # BFS on incidence graph
    dq = collections.deque([('p', a, 0)]); best = {}
    while dq:
        t, v, d = dq.popleft()
        if t == 'p':
            if v == b: return d
            for L in pl[v]:
                if L not in dist_l:
                    dist_l[L] = d + 1; dq.append(('l', L, d + 1))
        else:
            for x in lines[v]:
                if x not in dist_p:
                    dist_p[x] = d + 1; dq.append(('p', x, d + 1))
    return None
pd = collections.Counter(); ld = collections.Counter()
ptsf = [p for p, _ in flags]; lnsf = [l for _, l in flags]
def line_inc_dist(L1, L2):
    # distance between lines in incidence graph: 2 if concurrent, else via points
    if L1 == L2: return 0
    if set(lines[L1]) & set(lines[L2]): return 2
    # walk: L1 - x - K - y - L2 gives 4
    for x in lines[L1]:
        for K in pl[x]:
            if K != L1 and set(lines[K]) & set(lines[L2]): return 4
    return 6
for i, j in itertools.combinations(range(len(flags)), 2):
    pd[inc_dist(ptsf[i], ptsf[j])] += 1
    ld[line_inc_dist(lnsf[i], lnsf[j])] += 1
print("point pairwise incidence distances:", dict(sorted(pd.items())))
print("line pairwise incidence distances:", dict(sorted(ld.items())))
