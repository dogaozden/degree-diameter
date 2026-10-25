"""Unit requests "p t l" for udesign: unit points in the collinearity ball B2(p0) (pairwise distance <= 4) and unit lines
in B2(L0) (pairwise distance <= 4), k units per matching, no line with all its points (and no point with all its
lines) used by one matching.
Usage: python3 ureq.py GHFILE j k SEED > req.txt   [p0 = point 0, L0 = a line at distance 5 from p0]"""
import sys, random, collections
sys.path.insert(0, '..')
from ghtools import load_gh, bfs
ghf, j, k, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
P, q, lines, adj = load_gh(ghf)
p0 = 0
d0 = bfs(adj, p0)
L0 = next(L for L in range(P) if d0[P + L] == 5)
dL = bfs(adj, P + L0)
ballP = [x for x in range(P) if d0[x] <= 2]
ballL = [L for L in range(P) if dL[P + L] <= 2]
ptlines = collections.defaultdict(list)
for L, pts in enumerate(lines):
    for x in pts: ptlines[x].append(L)
out = []
for t in range(1, j + 1):
    for attempt in range(1000):
        ps = rng.sample(ballP, k); ls = rng.sample(ballL, k)
        sp = set(ps); sl = set(ls)
        if any(all(x in sp for x in lines[L]) for L in range(P) if d0[P + L] <= 3): continue
        if any(all(L in sl for L in ptlines[x]) for x in range(P) if dL[x] <= 3): continue
        break
    for p, L in zip(ps, ls): out.append((p, t, L))
for p, t, L in out: print(p, t, L)
print('p0=%d L0=%d |B2(p0)|=%d |B2(L0)|=%d units=%d' % (p0, L0, len(ballP), len(ballL), len(out)), file=sys.stderr)
