# Point-line incidence graph of the symplectic quadrangle W(q), q=16 (GF(16) via x^4+x+1).
# Points: 1-dim subspaces of GF(16)^4 ; lines: totally isotropic 2-dim subspaces (17 points each).
# Output: edge list, points 0..4368, lines 4369..8737. Expect 17-regular, girth 8, diameter 4.
import sys, itertools
import numpy as np
EXP = [0]*30; LOG = [0]*16
x = 1
for i in range(15):
    EXP[i] = x; LOG[x] = i
    x <<= 1
    if x & 16: x ^= 0b10011
for i in range(15, 30): EXP[i] = EXP[i-15]
MUL = [[(0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]) for b in range(16)] for a in range(16)]
MULA = np.array(MUL, dtype=np.int64)
def inv(a): return EXP[(15 - LOG[a]) % 15]
def norm(v):
    for c in v:
        if c:
            ic = inv(c); return tuple(MUL[ic][t] for t in v)
    return None
vecs = [v for v in itertools.product(range(16), repeat=4) if any(v)]
pts = sorted({norm(v) for v in vecs})
assert len(pts) == 4369
P = np.array(pts, dtype=np.int64)
pid = {p: i for i, p in enumerate(pts)}
def Bvec(p):  # symplectic form of p with all points (char 2: XOR)
    return (MULA[p[0], P[:, 1]] ^ MULA[p[1], P[:, 0]] ^ MULA[p[2], P[:, 3]] ^ MULA[p[3], P[:, 2]])
done = set()
lines = []
for i, p in enumerate(pts):
    perp = np.nonzero(Bvec(p) == 0)[0]
    for j in perp:
        j = int(j)
        if j == i or (i, j) in done: continue
        r = pts[j]
        span = set()
        for a in range(16):
            for b in range(16):
                w = tuple(MUL[a][p[k]] ^ MUL[b][r[k]] for k in range(4))
                if any(w): span.add(norm(w))
        L = sorted(pid[s] for s in span)
        assert len(L) == 17
        for u in L:
            for v in L:
                if u != v: done.add((u, v))
        lines.append(L)
assert len(lines) == 4369, len(lines)
with open(sys.argv[1], 'w') as f:
    f.write(f"{4369 + len(lines)}\n")
    for jx, L in enumerate(lines):
        for pp in L: f.write(f"{pp} {4369 + jx}\n")
print("points", len(pts), "lines", len(lines))
