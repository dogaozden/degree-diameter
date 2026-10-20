"""Describe a PG(2,q)+new graph saved by sat_ext.py: for each new vertex, its old incidences
in geometric terms (concurrent lines / collinear points), and the new-new incidences."""
import json, sys, itertools
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'plus2'))
from construction import pg_plane

f, q = sys.argv[1], int(sys.argv[2])
pts, lns = pg_plane(q)
N = len(pts)
n, E = json.load(open(f))['output']
nP = None
# sat_ext layout: points 0..NP-1 (old 0..N-1), then lines (old N..)
deg_side = {}
# recover kP from n and edges: lines start at index len(P)
maxp = max(u for u, v in E)
minl = min(v for u, v in E)
NP = minl
NL = n - NP
kP, kL = NP - N, NL - N
inc = set((u, v - NP) for u, v in E)
print(f'q={q} kP={kP} kL={kL}')
dels = [(p, l) for l in range(N) for p in lns[l] if (p, l) not in inc]
adds = [(p, l) for (p, l) in inc if p < N and l < N and p not in lns[l]]
print('deleted flags', dels, 'added', adds)
def line_of(x, y):
    return next(j for j in range(N) if x in lns[j] and y in lns[j])
for h in range(N, NP):
    ol = [l for l in range(N) if (h, l) in inc]
    nl = [l - N for l in range(N, NL) if (h, l) in inc]
    # concurrency: common points of the old lines
    common = set(pts)
    for l in ol: common &= lns[l]
    cnt = {}
    for l in ol:
        for x in lns[l]: cnt[x] = cnt.get(x, 0) + 1
    top = max(cnt.items(), key=lambda t: t[1]) if cnt else None
    print(f' new point H{h-N}: {len(ol)} old lines, max concurrency {top}, new lines K{nl}')
for K in range(N, NL):
    op = [p for p in range(N) if (p, K) in inc]
    npnt = [p - N for p in range(N, NP) if (p, K) in inc]
    cnt = {}
    for x, y in itertools.combinations(op, 2):
        l = line_of(x, y); cnt[l] = cnt.get(l, 0) + 1
    top = max(cnt.items(), key=lambda t: t[1]) if cnt else None
    # number of points on best line
    best = max((sum(1 for x in op if x in lns[l]), l) for l in range(N)) if op else None
    print(f' new line K{K-N}: {len(op)} old points, max collinear {best}, new points H{npnt}')

# copy configuration (Theorem thm:copies): X_h = point of max concurrency, L_K = line of max collinearity
print('copy configuration:')
X = {}
for h in range(N, NP):
    ol = [l for l in range(N) if (h, l) in inc]
    cnt = {}
    for l in ol:
        for x in lns[l]:
            cnt[x] = cnt.get(x, 0) + 1
    X[h] = max(cnt, key=cnt.get) if cnt else None
LK = {}
for K in range(N, NL):
    op = [p for p in range(N) if (p, K) in inc]
    LK[K] = max(range(N), key=lambda l: sum(1 for x in op if x in lns[l])) if op else None
for h in range(N, NP):
    x = X[h]
    missing = [l for l in range(N) if x in lns[l] and (h, l) not in inc]
    extra = [l for l in range(N) if (h, l) in inc and x not in lns[l]]
    newl = [K for K in range(N, NL) if (h, K) in inc]
    copied = {l: [K - N for K in newl if LK[K] == l] for l in missing}
    free = [K - N for K in newl if LK[K] not in missing]
    print(f' H{h-N} copies point {x}: missing lines {missing} copied by {copied}; extra old lines {extra}; free new lines {free}')
for K in range(N, NL):
    L0 = LK[K]
    missing = [x for x in lns[L0] if (x, K) not in inc]
    extra = [x for x in range(N) if (x, K) in inc and x not in lns[L0]]
    newp = [h for h in range(N, NP) if (h, K) in inc]
    copied = {x: [h - N for h in newp if X[h] == x] for x in missing}
    free = [h - N for h in newp if X[h] not in missing]
    print(f' K{K-N} copies line {L0}: missing points {missing} copied by {copied}; extra old points {extra}; free new points {free}')
xs = sorted(set(X.values())); ls_ = sorted(set(LK.values()))
print(' copied points', xs, 'copied lines', ls_)
print(' incidences among them:', [(x, l) for x in xs for l in ls_ if x in lns[l]])
