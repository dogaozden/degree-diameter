import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d12D7-r2/c8/src')
from q3lib import *
import itertools
LP = load_hex(); M = load_phi(); S = load_spread()
F = sorted(set(p for l in S for p in LP[l]))
n = NL * B
E = main_edges(LP, M, set(F))
adj = adjlist(n, E)
# distances from every freed point vertex (p,0) (level shift is an automorphism)
DP = {p: dist_from(adj, ID(p, 0)) for p in F}
# distances from line vertex (M(p),0)
DL = {p: dist_from(adj, ID(M[p], 0)) for p in F}
# ecc-cover test for owner-constant L(p): max over main vertices x of min_i d((p,i),x)
def cover_ok(D, p):
    # d((p,i),x) = d((p,0), (x shifted by -i)); evaluate over all x in all levels
    worst = 0
    for x in range(n):
        best = min(D[p][((x // B - i) % NL) * B + x % B] for i in range(NL))
        worst = max(worst, best)
    return worst
print('cover radius (L-hub owner-constant) over freed p:', sorted(set(cover_ok(DP, p) for p in F)))
print('cover radius (P-hub owner-constant) over freed p:', sorted(set(cover_ok(DL, p) for p in F)))
# pairwise owner distances
D = {}
for p in F:
    for pp in F:
        D[(p, pp)] = min(DP[p][ID(pp, s)] for s in range(NL))
vals = {}
for p in F:
    for pp in F:
        if p != pp: vals[D[(p, pp)]] = vals.get(D[(p, pp)], 0) + 1
print('LL owner distance histogram (ordered pairs, over shifts):', sorted(vals.items()))
Ev = {}
for p in F:
    for pp in F:
        e = min(DP[p][ID(N + M[pp], s)] for s in range(NL))
        Ev[(p, pp)] = e
hist = {}
for k, v in Ev.items(): hist[v] = hist.get(v, 0) + 1
print('LP owner distance histogram (point owner p, line-vertex M(pp)):', sorted(hist.items()))
