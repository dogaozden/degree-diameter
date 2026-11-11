#!/usr/bin/env python3
"""Independent sampling check of the statement Lemma44 of lean/BipartiteDD/LeanMaxx/Omega45b/PerpQuadric.lean (Lemma 4.4 of
research/theorems/OMEGA_REPAIR.md for q = 7): a collineation of H(7) that fixes no point moves at most 4144 points s to a
point h(s) with B(s, h s) = 0.  This is a SAMPLING check of the hypothesis, not a proof; the Lean files take Lemma44 as a hypothesis.
Collineations are produced as random products of long root elations x -> x + b(x,u) v - b(x,v) u, where (u,v) spans a line of H(7)
(a pair satisfying Q = 0, B = 0 and Tits' six equations, exactly the IsHPair of lean/BipartiteDD/Hexagon/Defs.lean).  The long root
groups generate G2(7) (7 is not a power of 3).  Each elation is first tested to map hexagon-line pairs to hexagon-line pairs."""
import random, sys
import numpy as np
q = 7
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
nel = int(sys.argv[2]) if len(sys.argv) > 2 else 8
ntry = int(sys.argv[3]) if len(sys.argv) > 3 else 200
rng = random.Random(seed)
allv = np.indices((q,)*7).reshape(7, -1).T.astype(np.int64)
Qv = (allv[:,0]*allv[:,4] + allv[:,1]*allv[:,5] + allv[:,2]*allv[:,6] - allv[:,3]**2) % q
Z = allv[Qv == 0]; nz = Z[(Z != 0).any(axis=1)]
inv = np.array([0,1,4,5,2,3,6])
def normalise(V):
    first = (V != 0).argmax(axis=1)
    lead = V[np.arange(len(V)), first]
    return (V * inv[lead][:, None]) % q
pts = np.unique(normalise(nz), axis=0); N = len(pts); assert N == 19608
pw = q ** np.arange(7)
code = pts @ pw
lookup = -np.ones(q**7, dtype=np.int64); lookup[code] = np.arange(N)
G = np.zeros((7,7), dtype=np.int64)  # Gram matrix of the polar form: b(x,y) = x^T G y
G[0,4]=G[4,0]=G[1,5]=G[5,1]=G[2,6]=G[6,2]=1; G[3,3]=(-2) % q
def b(x, y): return int(x @ G @ y) % q
def Qf(x): return int(x[0]*x[4]+x[1]*x[5]+x[2]*x[6]-x[3]*x[3]) % q
def tits(x, y):
    pl = lambda i, j: (x[i]*y[j] - x[j]*y[i]) % q
    return (pl(1,2)==pl(3,4) and pl(5,4)==pl(3,2) and pl(2,0)==pl(3,5) and pl(6,5)==pl(3,0) and pl(0,1)==pl(3,6) and pl(4,6)==pl(3,1))
def titsv(x, Y):  # vectorised in Y
    pl = lambda i, j: (x[i]*Y[:,j] - x[j]*Y[:,i]) % q
    return (pl(1,2)==pl(3,4)) & (pl(5,4)==pl(3,2)) & (pl(2,0)==pl(3,5)) & (pl(6,5)==pl(3,0)) & (pl(0,1)==pl(3,6)) & (pl(4,6)==pl(3,1))
def hex_partners(ui):
    u = pts[ui]
    perp = (pts @ (G @ u)) % q == 0
    m = perp & titsv(u, pts)
    m[ui] = False
    return np.nonzero(m)[0]
def line_pair(ui=None):
    while True:
        ui = rng.randrange(N)
        P = hex_partners(ui)
        if len(P): return ui, int(rng.choice(P))
# statistics: q+1 = 8 points per line, so each point u has (q+1)*q = 56 partners on its 8 lines
ui = rng.randrange(N); print("hexagon partners of a point (expect 8 lines x 7 other points = 56):", len(hex_partners(ui)))
def elation(u, v):
    Gu, Gv = G @ u, G @ v
    M = (np.eye(7, dtype=np.int64) + np.outer(v, Gu) - np.outer(u, Gv)) % q
    return M
def is_collineation_sample(M, ntest=40):
    # preserves Q and maps hexagon-line pairs to hexagon-line pairs
    for _ in range(ntest):
        ai, ci = line_pair()
        a, c = pts[ai], pts[ci]
        a2, c2 = (M @ a) % q, (M @ c) % q
        if Qf(a2) != 0 or Qf(c2) != 0 or b(a2, c2) != 0 or not tits(a2, c2): return False
    return True
good = 0
for _ in range(20):
    ui, vi = line_pair(); M = elation(pts[ui], pts[vi])
    good += is_collineation_sample(M, 25)
print("long root elations (hexagon-line axes) mapping sampled hexagon-line pairs to hexagon-line pairs: %d / 20" % good)
assert good == 20
# negative control: elation with an axis that is a totally singular line NOT in the hexagon
def bad_axis():
    while True:
        ui = rng.randrange(N); perp = np.nonzero(((pts @ (G @ pts[ui])) % q == 0))[0]
        vi = int(rng.choice(perp))
        if vi != ui and not tits(pts[ui], pts[vi]): return ui, vi
nb = 0
for _ in range(20):
    ui, vi = bad_axis(); nb += not is_collineation_sample(elation(pts[ui], pts[vi]), 25)
print("negative control: elations with a non-hexagon singular axis that FAIL to preserve the hexagon: %d / 20" % nb)
# random elements and Perp
def apply_pts(M):
    img = normalise((pts @ M.T) % q)
    return lookup[img @ pw]
def perp_count(M):
    idx = apply_pts(M); assert (idx >= 0).all()
    fixed = int((idx == np.arange(N)).sum())
    img = pts[idx]
    bv = np.einsum('ij,jk,ik->i', pts, G, img) % q
    return fixed, int((bv == 0).sum())
res = []
for _ in range(ntry):
    M = np.eye(7, dtype=np.int64)
    for _ in range(nel):
        ui, vi = line_pair(); M = (elation(pts[ui], pts[vi]) @ M) % q
    fx, pc = perp_count(M)
    res.append((fx, pc))
fpf = [pc for fx, pc in res if fx == 0]
print("random products of %d elations: %d sampled, %d fixed-point-free" % (nel, ntry, len(fpf)))
print("fixed-point counts histogram:", {k: sum(1 for f, _ in res if f == k) for k in sorted({f for f, _ in res})})
if fpf:
    print("fixed-point-free: |Perp(h)| min %d, max %d (Lemma 4.4 bound 4144)" % (min(fpf), max(fpf)))
    assert max(fpf) <= 4144
print("all-element |Perp| max (incl. elements with fixed points; Perp counts fixed points too):", max(pc for _, pc in res))
