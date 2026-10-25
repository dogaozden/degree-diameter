# Structure of a J-invariant partial ovoid in E = A (+) V4 (A = (x0,x3), V4 = (x1,x2,x5,x6)).
import sys
import numpy as np
from collections import Counter, defaultdict
q = int(sys.argv[2]) if len(sys.argv) > 2 else 11
C = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
pos = {int(r[0]): i for i, r in enumerate(rows)}
S = [pos[int(l.split()[0])] for l in open(sys.argv[1])]
X = rows[S][:, 2:9] % q
INV = [0] + [pow(a, q - 2, q) for a in range(1, q)]
def nrm(v):
    v = [int(x) % q for x in v]
    for x in v:
        if x: return tuple(y * INV[x] % q for y in v)
    return tuple(v)
dirA = Counter(); byA = defaultdict(list)
for x in X:
    a = (x[0], x[3]); w = (x[1], x[2], x[5], x[6])
    # scale so that a = (1, s) or (0, 1)
    if a[0]: s = INV[a[0]]
    else: s = INV[a[1]]
    an = nrm(a); wn = tuple(int(y) * s % q for y in w)
    QA = (-C * an[0] * an[0] - an[1] * an[1]) % q
    dirA[an] += 1; byA[an].append(wn)
print("points", len(X), "A-directions used:", len(dirA), sorted(dirA.values()))
# for each A-direction, span (rank) of its w-vectors and the projective w points
def rank(vs):
    A = np.array(vs, dtype=np.int64) % q; r = 0
    for c in range(A.shape[1]):
        piv = next((i for i in range(r, A.shape[0]) if A[i, c]), None)
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]; A[r] = (A[r] * INV[A[r, c]]) % q
        for i in range(A.shape[0]):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % q
        r += 1
    return r
for an, ws in sorted(byA.items()):
    pw = set(nrm(w) for w in ws)
    print(an, "count", len(ws), "distinct [w]", len(pw), "rank of w's", rank(ws), "rank of [w]s", rank(list(pw)))
