"""Class-0 walks in a Z_5 x B lift whose Z_5 part is the polygon cover (flags 0, hop s_k carries k).
For a point x and a line y at distance 3, the walks of length <= 7 with Z_5-voltage 0 are the geodesic, the
"cancelling" walks with two hops of the same matching in opposite directions, and walks with >= 3 hops.
Expected average for random matchings: 4(q+1)(3q^3+4q^2+2q-1)/(q^4+q^3+q^2+q+1) (two matchings, both directions).
This script (a) counts the cancelling walks directly for every pair at distance 3, and (b) checks the identity
  sum over pairs = sum_k sum_{u != w} [d(s_k u, s_k w) = 2] g2(d(u,w)) + [d(s_k u, s_k w) = 4] g4(d(u,w)) + (lines)
with g2(2) = 3q^2 - q, g2(4) = 3q - 1, g2(6) = 2(q+1), g4(2) = q, g4(4) = 1, g4(6) = 0.
usage: class0.py q seed [dual | base.txt]   (dual: s_1 = a duality from research/squads/r2-d8/d7/dual_q3_s1.npy, q = 3)"""
import sys
import random
import numpy as np
import gh
q, seed = int(sys.argv[1]), int(sys.argv[2])
rng = random.Random(seed)
H = gh.load(q)
N = H.N
Dm, adj = gh.distances(H)
Dm = Dm.astype(np.int64)
mats = []
if len(sys.argv) > 3 and sys.argv[3] not in ('dual',):
    # read the two hop matchings from a polygon-cover base file (Z_5 voltage 1 = s_1, 2 = s_2)
    hop = {1: np.zeros(N, dtype=np.int64), 2: np.zeros(N, dtype=np.int64)}
    with open(sys.argv[3]) as fh:
        fh.readline()
        for line in fh:
            u, v, a, b = map(int, line.split())
            if a in (1, 2):
                hop[a][u] = v - N
    mats = [hop[1], hop[2]]
for k in range(2 if not mats else 0):
    if len(sys.argv) > 3 and sys.argv[3] == 'dual' and k == 0:
        phi = np.load('/home/user/degree-diameter/research/squads/r2-d8/d7/dual_q3_s1.npy')
        s = np.array([int(phi[p]) - N for p in range(N)])
    else:
        s = np.array(rng.sample(range(N), N))
    mats.append(s)
pts = np.arange(N)
g2 = {2: 3 * q * q - q, 4: 3 * q - 1, 6: 2 * (q + 1)}
g4 = {2: q, 4: 1, 6: 0}
pred = 0
direct = 0
perpair = np.zeros((N, N), dtype=np.int64)
for s in mats:
    sinv = np.empty(N, dtype=np.int64)
    sinv[s] = pts
    SL = N + s  # line vertex of s(u)
    dS = Dm[np.ix_(SL, SL)]          # d(s u, s w) for points u, w
    dP = Dm[:N, :N]                   # d(u, w)
    for delta, gtab in ((2, g2), (4, g4)):
        for d, val in gtab.items():
            pred += val * int(np.sum((dS == delta) & (dP == d)))
    # line version: backward hop first: x ~ b (line) -> s^{-1}(b) ~ ... ~ w' -> s(w') ~ y ; pairs of lines (b, b')
    PB = sinv  # point s^{-1}(line k)
    dSP = Dm[np.ix_(PB, PB)]          # d(s^{-1} b, s^{-1} b')
    dL = Dm[N:, N:]
    for delta, gtab in ((2, g2), (4, g4)):
        for d, val in gtab.items():
            pred += val * int(np.sum((dSP == delta) & (dL == d)))
    # direct count over pairs (x point, y line) at distance 3
    Dpl = Dm[:N, N:]
    for x in range(N):
        ys = np.nonzero(Dpl[x] == 3)[0]
        # forward first: x ~a~ u -> s(u) ~b~ s(w) -> w ~c~ y with a+b+c <= 5, b in {2,4}
        du = Dm[x, :N]                     # d(x,u)
        for b in (2, 4):
            U, W = np.nonzero(dS == b)
            ok = du[U] + b <= 4            # need a + b + c <= 5 with c >= 1
            U, W = U[ok], W[ok]
            if len(U) == 0:
                continue
            a = du[U]
            c = Dpl[W][:, ys]              # d(w, y) for each candidate y
            hit = (a[:, None] + b + c) <= 5
            direct += int(np.sum(hit)); perpair[x, ys] += hit.sum(axis=0)
        # backward first: x ~a~ b1 -> s^{-1}(b1) ~b~ s^{-1}(b2) -> b2 ~c~ y, a odd, b even >= 2, c even
        dxl = Dm[x, N:]
        for b in (2, 4):
            B1, B2 = np.nonzero(dSP == b)
            ok = dxl[B1] + b <= 5
            B1, B2 = B1[ok], B2[ok]
            if len(B1) == 0:
                continue
            a = dxl[B1]
            c = Dm[np.ix_(N + B2, N + ys)]
            hit = (a[:, None] + b + c) <= 5
            direct += int(np.sum(hit)); perpair[x, ys] += hit.sum(axis=0)
npairs = N * q * q * (q + 1)
vals = perpair[Dm[:N, N:] == 3]
import collections
hist = sorted(collections.Counter(vals.tolist()).items())
print('per-pair cancelling-walk counts (count: number of pairs), min', vals.min(), ':', hist[:12], '...')
print(f'q {q} seed {seed} matchings {sys.argv[3] if len(sys.argv) > 3 else "random"}: cancelling walks over '
      f'{npairs} pairs at distance 3: direct {direct}, formula {pred}, average {direct / npairs:.3f}')
