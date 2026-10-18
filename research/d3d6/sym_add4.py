"""For every degree-feasible symmetric 3-gadget frame (A=0), count 4th-gadget frames that keep loads <= 2.
python3 sym_add4.py q"""
import itertools, json, sys
from singer import singer_plane
q = int(sys.argv[1]); points, lines = singer_plane(q); n = len(points); s3 = n // 3
thru = [[j for j in range(n) if p in lines[j]] for p in points]
LT = {}
for j, L in enumerate(lines):
    for a, b in itertools.combinations(sorted(L), 2): LT[a, b] = j
lt = lambda a, b: LT[min(a, b), max(a, b)]
def loadsets(A, ell, X):
    P = set(lines[ell])
    for x in X: P |= lines[lt(A, x)]
    L = set(thru[A])
    for x in X: L |= set(thru[x])
    return P, L
best = 0
for ell in range(n):
    if 0 in lines[ell]: continue
    for X in itertools.combinations(sorted(lines[ell]), 4):
        lp = [0] * n; ll = [0] * n; ok = True; frs = []
        for t in (0, s3, 2 * s3):
            A2, e2, X2 = t % n, (ell + t) % n, [(x + t) % n for x in X]
            frs.append((A2, e2, X2))
            P, L = loadsets(A2, e2, X2)
            for x in P: lp[x] += 1
            for x in L: ll[x] += 1
        if max(lp) > 2 or max(ll) > 2: continue
        okP = {p for p in points if lp[p] <= 1}; okL = {j for j in range(n) if ll[j] <= 1}
        cnt = 0; sample = None
        for A in points:
            if not all(j in okL for j in thru[A]): continue
            for e in range(n):
                if A in lines[e] or not lines[e] <= okP: continue
                good = [x for x in lines[e] if lines[lt(A, x)] <= okP and all(j in okL for j in thru[x])]
                if len(good) >= 4:
                    cnt += 1; sample = sample or (A, e, good)
        if cnt:
            print('3-frame', ell, X, '4th options', cnt, sample, flush=True); best += 1
print('configs with a 4th gadget:', best)
