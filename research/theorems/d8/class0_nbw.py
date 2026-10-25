"""Exact upper bound for the Z_K part of a Z_5 x Z_K lift whose Z_5 quotient X is given (liftdiam base with M2 = 1
or any M2; only the Z_5 voltages a are used): for a point x and a line y, the copies (y,(0,b)) need reduced walks of
length <= 7 from (x,0) to (y,0) in X with different Z_K voltages, so K <= 1 + ... <= NBW(x,y) := number of
non-backtracking walks of length <= 7 from (x,0) to (y,0) in X.  Prints min and histogram of NBW over point-line
pairs (all sources x), split by the H(q)-distance of x and y.  usage: class0_nbw.py base.txt q [source_step]"""
import sys
import collections
import numpy as np
import gh
path, q = sys.argv[1], int(sys.argv[2])
STEP = int(sys.argv[3]) if len(sys.argv) > 3 else 1
with open(path) as fh:
    NB, M1, M2, E = map(int, fh.readline().split())
    ed = [tuple(map(int, l.split())) for l in fh]
assert M1 == 5
N = NB // 2
# darts of X: vertex (v, g) index v*5+g ; edge (u,v,a): (u,g)->(v,g+a) and reverse
tails, heads = [], []
for (u, v, a, b) in ed:
    for g in range(5):
        tails.append(u * 5 + g); heads.append(v * 5 + (g + a) % 5)
nd = len(tails)
tails = np.array(tails + heads); heads2 = np.array(heads + tails[:nd].tolist())
heads = heads2
rev = np.concatenate([np.arange(nd, 2 * nd), np.arange(nd)])
nv = NB * 5
H = gh.load(q)
Dm = None
if N <= 4000:
    Dm, _ = gh.distances(H)
res = collections.defaultdict(list)
for x in range(0, N, STEP):
    src = x * 5
    cur = (tails == src).astype(np.int64)  # walks of length 1 ending with dart d
    tot = np.zeros(nv, dtype=np.int64)
    np.add.at(tot, heads, cur)
    for L in range(2, 8):
        S = np.bincount(heads, weights=cur, minlength=nv).astype(np.int64)
        cur = S[tails] - cur[rev]
        if L % 2 == 1:
            np.add.at(tot, heads, cur)
    if Dm is not None:
        dl = Dm[x, N:]
    else:
        import collections as _c
        dist = {x: 0}; dq = _c.deque([x]); dl = np.zeros(N, dtype=np.int64)
        adjP = H.through; adjL = H.lines
        while dq:
            v = dq.popleft()
            if v < N:
                for k in adjP[v]:
                    w = N + int(k)
                    if w not in dist: dist[w] = dist[v] + 1; dq.append(w)
            else:
                for p in adjL[v - N]:
                    p = int(p)
                    if p not in dist: dist[p] = dist[v] + 1; dq.append(p)
        for k in range(N): dl[k] = dist[N + k]
    for y in range(N):
        res[int(dl[y])].append(int(tot[(N + y) * 5]))
for d in sorted(res):
    a = np.array(res[d])
    h = sorted(collections.Counter(a.tolist()).items())
    print(f'd(x,y) = {d}: pairs {len(a)}, NBW to the same Z_5-copy: min {a.min()}, mean {a.mean():.1f}, smallest values {h[:6]}')
