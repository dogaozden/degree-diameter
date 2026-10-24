import sys, numpy as np, itertools
sys.path.insert(0, '../tools'); import hexlib
from f9 import *
q, lines, coord = hexlib.load('../hex/hex_q9.bin'); P = coord.astype(np.int64); N = len(P)
code = P @ (9 ** np.arange(7))
def idx(v):
    v = np.array(v) % 9; f = np.nonzero(v)[0][0]; v = M[INV[v[f]], v]
    k = int(v @ (9 ** np.arange(7))); j = int(np.searchsorted(code, k)); assert code[j] == k; return j
pl = hexlib.point_lines(lines, N)
lineset = {tuple(sorted(l)): i for i, l in enumerate(lines.tolist())}
E = np.eye(7, dtype=np.int64)
cpts = {i: idx(E[i]) for i in [0, 1, 2, 4, 5, 6]}
def common_line(a, b):
    s = set(pl[a].tolist()) & set(pl[b].tolist()); return s.pop() if s else None
coll = {(i, j): common_line(cpts[i], cpts[j]) for i in cpts for j in cpts if i < j}
print('collinear coordinate pairs:', [k for k, v in coll.items() if v is not None])
# build the cycle of the standard apartment
adj = {i: [j for j in cpts if j != i and coll[tuple(sorted((i, j)))] is not None] for i in cpts}
cyc = [0]
while len(cyc) < 6:
    nxt = [j for j in adj[cyc[-1]] if j not in cyc][0]; cyc.append(nxt)
print('apartment cycle of coordinate points:', cyc)
alines = [coll[tuple(sorted((cyc[k], cyc[(k + 1) % 6])))] for k in range(6)]   # line between a_k and a_{k+1}
img = np.load('line_image.npy')   # image point (in W/I coords) of every line
# image apartment: z_k = image of line alines[k]; image-hexagon line through z_{k-1}, z_k = image of pencil of a_k
z = img[alines]
Rz, _ = rref(z.copy()); print('rank of the 6 image points:', len(Rz))
# Gram of the induced form on W/I: we need B_W on W/I coordinates.  Lift: W/I coords -> pick preimages in W.
Pi = np.load('Pi.npy'); Wb = np.load('Wbasis.npy'); G21 = np.load('G21.npy')
# section s: F^7 -> F^14 with Pi s = id (solve Pi X = I)
S = np.zeros((14, 7), np.int64)
Raug, piv = rref(np.concatenate([Pi, np.eye(7, dtype=np.int64)], 1).copy())
for r, p in enumerate(piv[:7]): S[p] = Raug[r, 14:]
def toW(v7):  # W/I coords -> a vector of Lambda^2 (21)
    c = np.zeros(14, np.int64)
    for k in range(7): c = A[c, M[S[:, k], v7[k]]]
    w = np.zeros(21, np.int64)
    for i in range(14): w = A[w, M[Wb[i], c[i]]]
    return w
def BW(u, v):
    a, b = toW(u), toW(v); s = 0
    for i in range(21):
        if a[i]:
            for j in range(21):
                if b[j]: s = A[s, M[M[a[i], G21[i, j]], b[j]]]
    return s
GZ = np.array([[BW(z[i], z[j]) for j in range(6)] for i in range(6)])
print('image apartment Gram (nonzero = opposite):\n', (GZ != 0).astype(int))
# 7th vector: w spanning U^perp, U = span(z)
Gfull = np.array([[BW(E[i], E[j]) for j in range(7)] for i in range(7)])
# U^perp: v with BW(z_k, v) = 0 for all k  ->  z Gfull v = 0
w = nullspace(np.array([[ (lambda r: r)(0) ] ]) if False else np.array([[int(x) for x in row] for row in [[0]*7]]))
ZG = np.zeros((6, 7), np.int64)
for k in range(6):
    for j in range(7):
        s = 0
        for i in range(7): s = A[s, M[z[k, i], Gfull[i, j]]]
        ZG[k, j] = s
w = nullspace(ZG); assert len(w) == 1; w = w[0]
Bww = BW(w, w)
a = E[cyc]                              # a_k = coordinate vectors
e3 = E[3]
B33 = Bf(e3, e3)
print('B_W(w,w) =', Bww, ' B(e3,e3) =', B33)
np.save('apt.npy', np.array(cyc)); np.save('alines.npy', np.array(alines))
# candidate psi: z_k -> lam_k a_k, w -> mu e3, possibly after Frobenius on W/I coordinates
pencils = {}
def check(psi_mat, frob, pts_sample):
    """does psi map image-hexagon lines (pencil images) to lines of H(9)? test on a sample of points"""
    for p in pts_sample:
        V = img[pl[p]]
        if frob: V = FROB[V]
        Y = np.zeros((len(V), 7), np.int64)
        for r in range(7):
            s = np.zeros(len(V), np.int64)
            for c in range(7): s = A[s, M[psi_mat[r, c], V[:, c]]]
            Y[:, r] = s
        ids = []
        for y in Y:
            f = np.nonzero(y)[0][0]; y = M[INV[y[f]], y]; k = int(y @ (9 ** np.arange(7)))
            j = int(np.searchsorted(code, k))
            if j >= N or code[j] != k: return False
            ids.append(j)
        if tuple(sorted(ids)) not in lineset: return False
    return True
rng = np.random.default_rng(3); sample = rng.choice(N, 6, replace=False)
found = None
Zb = np.concatenate([z, w[None, :]], 0).T     # columns: z_0..z_5, w  (basis of W/I)
for frob in (0, 1):
    Zf = FROB[Zb] if frob else Zb
    # inverse of the basis matrix (as columns)
    Raug, piv = rref(np.concatenate([Zf, np.eye(7, dtype=np.int64)], 1).copy())
    if len(piv) < 7 or piv[:7] != list(range(7)): continue
    Zinv = Raug[:, 7:]
    for lam in itertools.product(range(1, 9), repeat=6):
        for mu in range(1, 9):
            T = np.zeros((7, 7), np.int64)   # columns: images of basis vectors
            for k in range(6): T[:, k] = M[lam[k], a[k]]
            T[:, 6] = M[mu, e3]
            # psi = T * Zinv
            psi = np.zeros((7, 7), np.int64)
            for r in range(7):
                for c in range(7):
                    s = 0
                    for t in range(7): s = A[s, M[T[r, t], Zinv[t, c]]]
                    psi[r, c] = s
            if check(psi, frob, sample[:2]) and check(psi, frob, sample):
                found = (psi, frob, lam, mu); break
        if found: break
    if found: break
print('found:', None if found is None else (found[1], found[2], found[3]))
if found: np.save('psi.npy', found[0]); np.save('psi_frob.npy', np.array([found[1]]))
