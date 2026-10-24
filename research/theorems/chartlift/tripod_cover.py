"""Exact cover: can PG(3,q) be partitioned into q+1 'q-pods' (an apex plus q lines through it)?  Reports counts of
partitions with all pods non-planar (lines spanning the space) vs with some planar pod.  Used for the (k, q) = (q+1, q)
perfect-chart question (CHART_LIFTS.md).  usage: python3 tripod_cover.py q"""
import sys, itertools
from gf import GF
q = int(sys.argv[1]); F = GF(q)
vecs = [v for v in itertools.product(range(q), repeat=4) if any(v)]
pts = sorted({F.canon(v) for v in vecs}); idx = {p: i for i, p in enumerate(pts)}; NP = len(pts)
def line(p, r):
    return frozenset(idx[F.canon(F.vadd(F.vscale(a, p), F.vscale(b, r)))] for a in range(q) for b in range(q) if a or b)
lines = sorted({line(pts[i], pts[j]) for i in range(NP) for j in range(i + 1, NP)}, key=sorted)
through = [[L for L in lines if i in L] for i in range(NP)]
pods = []
for a in range(NP):
    for trip in itertools.combinations(through[a], q):
        S = frozenset().union(*trip)
        if len(S) != q * q + 1: continue
        # planar iff all points lie in a plane: rank of the point set
        rk = F.rank([pts[i] for i in S])
        pods.append((S, a, rk == 3))
print('q', q, 'points', NP, 'lines', len(lines), 'pods', len(pods), 'planar', sum(p[2] for p in pods))
by_point = [[] for _ in range(NP)]
for t, (S, a, pl) in enumerate(pods):
    for i in S: by_point[i].append(t)
found = {'nonplanar': 0, 'mixed': 0, 'planar': 0}; examples = {}
def dfs(covered, chosen):
    if len(chosen) == q + 1:
        if len(covered) == NP:
            kinds = [pods[t][2] for t in chosen]
            key = 'planar' if all(kinds) else ('nonplanar' if not any(kinds) else 'mixed')
            found[key] += 1; examples.setdefault(key, list(chosen))
        return
    p = next(i for i in range(NP) if i not in covered)
    for t in by_point[p]:
        S = pods[t][0]
        if S & covered: continue
        if chosen and t < chosen[-1] and False: continue
        dfs(covered | S, chosen + [t])
dfs(frozenset(), [])
print('partitions found (ordered by first-uncovered point, so each counted once):', found)
for key, ex in examples.items():
    print(key, 'apexes', [pts[pods[t][1]] for t in ex])
