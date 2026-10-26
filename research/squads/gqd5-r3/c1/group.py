# Card r3c1: stabiliser of the regular spread S of W(9) inside the Siegel parabolic [[A,B],[0,mu*A^{-T}]], B = S0 D / mu.
# Writes H1.npy (array of permutations of the 820 points, one row each) and prints the group order.
import sys, itertools, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import W, regular_spread_W
q = 9
G = W(q); F = G.F
add = np.array(F.add); mul = np.array(F.mul); inv = np.array([0] + F.inv[1:])
neg = np.array(F.neg)
pts = np.array(G.coords, dtype=np.int64)          # (820,4)
n = G.np
S = regular_spread_W(G)
sline = np.full(n, -1)
for k, L in enumerate(S):
    for p in G.lines[L]: sline[p] = k
assert (sline >= 0).all()
rep = np.array([G.lines[L][0] for L in S])
code = np.array([9 ** 3, 9 ** 2, 9, 1])
lut = np.full(9 ** 4, -1); lut[(pts * code).sum(1)] = np.arange(n)

def apply(M):
    W_ = np.zeros((n, 4), dtype=np.int64)
    for j in range(4):
        acc = np.zeros(n, dtype=np.int64)
        for i in range(4):
            acc = add[acc, mul[pts[:, i], M[i][j]]]
        W_[:, j] = acc
    f = (W_ != 0).argmax(axis=1)
    s = W_[np.arange(n), f]
    W_ = mul[inv[s][:, None], W_]
    return lut[(W_ * code).sum(1)]

def preserves_S(img):
    f = sline[img]
    return np.array_equal(f, f[rep[sline]])

# 2x2 helpers
def det2(a, b, c, d): return F.sub[mul[a][d]][mul[b][c]]
def inv2(a, b, c, d):
    di = inv[det2(a, b, c, d)]
    return (mul[di][d], mul[di][neg[b]], mul[di][neg[c]], mul[di][a])
def T2(a, b, c, d): return (a, c, b, d)

# nonsquare
nonsq = next(x for x in range(1, q) if all(mul[y][y] != x for y in range(1, q)))
mus = [1, nonsq]
# symmetric S0 = [[s0, s1], [s1, s2]]
sym = [(s0, s1, s1, s2) for s0 in range(q) for s1 in range(q) for s2 in range(q)]
found = {}
cnt = 0
for A in itertools.product(range(q), repeat=4):
    nzs = [x for x in A if x]
    if not nzs or nzs[0] != 1: continue
    if det2(*A) == 0: continue
    Ai = inv2(*A); AiT = T2(*Ai)            # A^{-T}
    for mu in mus:
        D = tuple(mul[mu][x] for x in AiT)  # mu A^{-T}
        Dinv_like = inv2(*D)                # D^{-1}
        for S0 in sym:
            # B = S0 * D / mu ... derived as B = S0 A^{-T} (mu absorbed): check symplecticity numerically below
            Bm = [[S0[0], S0[1]], [S0[2], S0[3]]]
            Dm = [[D[0], D[1]], [D[2], D[3]]]
            # B = S0 * (A^{-T}) with mu: use B = S0 * D * mu^{-1}
            muinv = inv[mu]
            Bv = []
            for i in range(2):
                for j in range(2):
                    acc = 0
                    for k in range(2):
                        acc = add[acc][mul[Bm[i][k]][Dm[k][j]]]
                    Bv.append(mul[acc][muinv])
            M = [[A[0], A[1], Bv[0], Bv[1]], [A[2], A[3], Bv[2], Bv[3]], [0, 0, D[0], D[1]], [0, 0, D[2], D[3]]]
            cnt += 1
            img = apply(M)
            if not preserves_S(img): continue
            key = img.tobytes()
            if key not in found: found[key] = img
print('candidates', cnt, 'S-preserving distinct perms', len(found), flush=True)
H = np.array(list(found.values()))
np.save('/home/user/degree-diameter/research/squads/gqd5-r3/c1/H1.npy', H)
# sanity: collinearity preserved for a few elements
col = G.col
for g in H[:20]:
    assert np.array_equal(col[np.ix_(g, g)], col)
print('collinearity check ok; group order (this parabolic part) =', len(H))
