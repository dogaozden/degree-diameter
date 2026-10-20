"""Check Lemma herm (a)-(e) and the whisker counts for even q."""
import sys
import numpy as np
from frame import Frame
q = int(sys.argv[1])
Fr = Frame(q)
H, N, lines, dist = Fr.H, Fr.N, Fr.H.lines, Fr.dist
print('q', q, 'delta', Fr.delta, 'v', Fr.v, 'max dist', dist.max())
S = Fr.S
print('|S|', len(S), 'expect', q**3 + 1, 'v in S', Fr.v in set(S.tolist()))
print('points of Pi', int(Fr.inPi.sum()), 'expect', (q**3 + 1) * (q + 1), 'covered once by S', int((Fr.Sline_of >= 0).sum()))
Sd = dist[N + S]
print('S lines distances from v', np.unique(Sd, return_counts=True))
print('free points', len(Fr.free), 'expect', q**3 * (q*q - 1))
# (d) points with X2 = X5 = 0 = points at distance <= 3 from v
z25 = (H.P[:, 2] == 0) & (H.P[:, 5] == 0)
print('(d) X2=X5=0 <=> dist<=3:', bool(np.all(z25 == (dist[:N] <= 3))), '; such points in Pi are on v:',
      bool(np.all(Fr.inPi[z25] == np.isin(np.arange(N), lines[Fr.v])[z25])))
allS = {}
ok = True
for a in range(q):
    for b in range(q):
        Sz = Fr.Sz(a, b)
        if len(Sz) != q**3 + 1 or Fr.v not in set(Sz.tolist()):
            ok = False
        cov = np.zeros(N, int)
        for s in Sz:
            cov[lines[s]] += 1
        inz = Fr.lin(H.P, a, b) == 0
        if not (np.all(cov[inz] == 1) and np.all(cov[~inz] == 0) and np.all(dist[N + Sz[Sz != Fr.v]] == 6)):
            ok = False
        allS[(a, b)] = set(Sz.tolist()) - {Fr.v}
print('(a,b) every S_z is a spread of Pi_z, size q^3+1, lines opposite v:', ok)
U = set()
tot = 0
for s in allS.values():
    tot += len(s)
    U |= s
print('(e) S_z pairwise meet only in v:', tot == len(U))
cand = set()
for z, s in allS.items():
    if z != (0, 0):
        cand |= s
opp = set(np.nonzero(dist[N:] == 6)[0].tolist()) - set(S.tolist())
print('candidates = lines opposite v not in S:', cand == opp, len(cand), 'expect', q**5 - q**3)
# each free point on exactly q candidates
cnt = np.zeros(N, int)
for k in cand:
    cnt[lines[k]] += 1
print('each free point on q candidates:', bool(np.all(cnt[Fr.free] == q)))
