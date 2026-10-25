# prep.py (card c3): Hermitian field-reduction candidates for H(8) partial ovoids.
# GF(8) = GF(2)[x]/(x^3+x+1), element a0+2a1+4a2. GF(64) = GF(8)[w], w^2 = w+1 (pairs (a,b) = a + b w).
# Hermitian form h(x,y) = sum_k x_k sigma(y_k), sigma(a+bw) = (a+b) + b w (= z^8).
# Tr(z) = b-coordinate of z. For x=(a_k,b_k), x'=(c_k,d_k): Tr(x sigma(x')) = a d + b c, so
# B(u,u') = sum_k (a_k d_k + b_k c_k) is the standard symplectic form on GF(8)^6 in coordinates (a1,b1,a2,b2,a3,b3).
# Hermitian curve: sum_k N(x_k) = 0, N(a+bw) = a^2+ab+b^2. Each curve point gives 9 GF(8)-points lambda*x, lambda in Lam.
# H(8) identification (README): (X0,X1,X2,X4,X5,X6) = (a1,a2,a3,b1,b2,b3), X3 = sqrt(X0X4+X1X5+X2X6) = (...)^4.
import numpy as np, struct, sys
D = '/home/user/degree-diameter/research/squads/d10D7-r5/c3/'
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'

MUL8 = np.zeros((8, 8), dtype=np.int64)
for x in range(8):
    for y in range(8):
        a = [(x >> i) & 1 for i in range(3)]; b = [(y >> i) & 1 for i in range(3)]
        r = [0] * 5
        for i in range(3):
            for j in range(3): r[i + j] ^= a[i] & b[j]
        for k in (4, 3):
            if r[k]: r[k] = 0; r[k - 3] ^= 1; r[k - 2] ^= 1
        MUL8[x, y] = r[0] | (r[1] << 1) | (r[2] << 2)
INV8 = {x: y for x in range(1, 8) for y in range(1, 8) if MUL8[x, y] == 1}
def m8(x, y): return int(MUL8[x, y])
def sq4(z):  # z^4 = sqrt(z) in GF(8)
    return m8(m8(z, z), m8(z, z))
def mul64(p, q, r, s):  # (p+qw)(r+sw), w^2=w+1
    return (m8(p, r) ^ m8(q, s), m8(p, s) ^ m8(q, r) ^ m8(q, s))
def norm64(a, b):  # z^9 = a^2+ab+b^2
    return m8(a, a) ^ m8(a, b) ^ m8(b, b)

# Lam: 9 representatives of GF(64)*/GF(8)*
LAM = [(1, 0)] + [(a, 1) for a in range(8)]

# Hermitian points (normalised: first nonzero GF(64) coordinate = 1)
pts = []
for v in range(8 ** 6):
    c = [((v >> (6 * k)) & 7, (v >> (6 * k + 3)) & 7) for k in range(3)]
    # sum_k N(x_k)
    nn = 0
    for (a, b) in c: nn ^= norm64(a, b)
    if nn: continue
    first = next(((a, b) for (a, b) in c if (a, b) != (0, 0)), None)
    if first != (1, 0): continue
    pts.append(c)
print('Hermitian points:', len(pts))
assert len(pts) == 513
# check h(x,y) != 0 for distinct curve points (pairwise non-orthogonal for h)
def h(x, y):
    s = (0, 0)
    for k in range(3):
        a, b = x[k]; c, d = y[k]
        sc = (c ^ d, d)  # sigma(c+dw)
        p = mul64(a, b, sc[0], sc[1]); s = (s[0] ^ p[0], s[1] ^ p[1])
    return s
bad = sum(1 for i in range(513) for j in range(i + 1, 513) if h(pts[i], pts[j]) == (0, 0))
print('pairs with h=0 among curve points:', bad)

# 4617 vertices: v = 9*i + t, GF(8)-vector u = coords of Lam[t]*x_i as (a1,b1,a2,b2,a3,b3)
U = np.zeros((513 * 9, 6), dtype=np.int64)
for i, x in enumerate(pts):
    for t, (p, q) in enumerate(LAM):
        row = []
        for k in range(3):
            a, b = x[k]
            ra, rb = mul64(p, q, a, b)
            row += [ra, rb]
        U[9 * i + t] = row
# B on vectors
def Bmat(U1, U2):  # all-pairs via broadcasting, returns uint8 matrix
    a1, b1, a2, b2, a3, b3 = [U1[:, c] for c in range(6)]
    c1, d1, c2, d2, c3, d3 = [U2[:, c] for c in range(6)]
    r = MUL8[a1[:, None], d1[None, :]] ^ MUL8[b1[:, None], c1[None, :]]
    r ^= MUL8[a2[:, None], d2[None, :]] ^ MUL8[b2[:, None], c2[None, :]]
    r ^= MUL8[a3[:, None], d3[None, :]] ^ MUL8[b3[:, None], c3[None, :]]
    return r
M = 513 * 9
Bv = np.zeros((M, M), dtype=np.uint8)
for s0 in range(0, M, 1024):
    Bv[s0:s0 + 1024] = Bmat(U[s0:s0 + 1024], U)
assert (Bv == Bv.T).all(), 'not symmetric'
grp = np.arange(M) // 9
same = grp[:, None] == grp[None, :]
print('same-group nonzero B entries:', int(((Bv != 0) & same).sum()), '(expect 0)')
conf = (Bv == 0) & ~np.eye(M, dtype=bool)
deg = conf.sum(1)
print('conflict degree min/max:', deg.min(), deg.max(), '(expect 520)')
cross = (conf & ~same).sum(1)
print('cross-conflict degree min/max:', cross.min(), cross.max(), '(expect 512)')
# conflict lists
L = np.full((M, 520), 0xFFFF, dtype=np.uint16)
for v in range(M):
    nb = np.nonzero(conf[v])[0]
    L[v, :len(nb)] = nb
    if len(nb) != 520: print('bad degree at', v, len(nb)); sys.exit(1)
L.tofile(D + 'conf_lists_u16.bin')
np.save(D + 'U.npy', U)
# H(8) ids via README coordinates
raw = open(HEX, 'rb').read()
hdr = struct.unpack('<iii', raw[:12]); q, N = hdr[0], hdr[1]
assert q == 8 and N == 37449
off = 12 + N * 9 * 4
X = np.frombuffer(raw[off:off + N * 7], dtype=np.uint8).reshape(N, 7).astype(np.int64)
# normalised check
fn = np.array([row[np.nonzero(row)[0][0]] for row in X])
assert (fn == 1).all(), 'file coordinates not normalised'
key_file = X[:, 0] + 8 * X[:, 1] + 64 * X[:, 2] + 512 * X[:, 3] + 4096 * X[:, 4] + 32768 * X[:, 5] + 262144 * X[:, 6]
lut = np.full(8 ** 7, -1, dtype=np.int64); lut[key_file] = np.arange(N)
# quadric check on file
q_ok = (MUL8[X[:, 0], X[:, 4]] ^ MUL8[X[:, 1], X[:, 5]] ^ MUL8[X[:, 2], X[:, 6]]) == MUL8[X[:, 3], X[:, 3]]
print('file quadric check all ok:', bool(q_ok.all()))
X0, X1, X2, X4, X5, X6 = U[:, 0], U[:, 2], U[:, 4], U[:, 1], U[:, 3], U[:, 5]
Xs = np.zeros((M, 7), dtype=np.int64)
Xs[:, 0] = X0; Xs[:, 1] = X1; Xs[:, 2] = X2; Xs[:, 4] = X4; Xs[:, 5] = X5; Xs[:, 6] = X6
qv = MUL8[X0, X4] ^ MUL8[X1, X5] ^ MUL8[X2, X6]
Xs[:, 3] = [sq4(int(z)) for z in qv]
# normalise: first nonzero coordinate -> 1
for v in range(M):
    row = Xs[v]
    f = next(int(z) for z in row if z)
    if f != 1:
        inv = INV8[f]
        Xs[v] = [m8(inv, int(z)) for z in row]
key_v = Xs[:, 0] + 8 * Xs[:, 1] + 64 * Xs[:, 2] + 512 * Xs[:, 3] + 4096 * Xs[:, 4] + 32768 * Xs[:, 5] + 262144 * Xs[:, 6]
ids = lut[key_v]
print('vertices mapped to H(8) ids: missing =', int((ids < 0).sum()), ' distinct =', len(set(ids.tolist())))
# verify: H(8) opposite <=> B_R != 0 on the lifted points (char 2, X3 term vanishes)
ii = ids
Xf = X[ii]
BR = MUL8[Xf[:, 0][:, None], Xf[:, 4][None, :]] ^ MUL8[Xf[:, 4][:, None], Xf[:, 0][None, :]]
BR ^= MUL8[Xf[:, 1][:, None], Xf[:, 5][None, :]] ^ MUL8[Xf[:, 5][:, None], Xf[:, 1][None, :]]
BR ^= MUL8[Xf[:, 2][:, None], Xf[:, 6][None, :]] ^ MUL8[Xf[:, 6][:, None], Xf[:, 2][None, :]]
print('B_R agrees with B on all vertex pairs:', bool(((BR == 0) == (Bv == 0)).all() ))
np.savetxt(D + 'vert_h8ids.txt', ids, fmt='%d')
np.save(D + 'vert_h8ids.npy', ids)
print('done')
