#!/usr/bin/env python3
"""orb8.py (card c1, squad round 5): orbit unions for pairwise-opposite point sets of H(8), GF(8) arithmetic.

Port of research/squads/d13D7_r4/c3/orbq.py (prime q) to q = 8.
GF(8): element = bit vector b0 + 2 b1 + 4 b2 (polynomial in alpha, alpha^3 = alpha + 1, reduction by x^3+x+1 = 11);
addition = XOR, multiplication = table MUL (as hexgen2.c).
Points of H(8) = points of Q(6,8): Q(x) = x0x4 + x1x5 + x2x6 + x3^2 = 0 in PG(6,8), first nonzero coordinate 1,
sorted by code sum x_i 8^i (research/d13D7/hex/hex_q8.bin, 37,449 points).
Opposite iff B(x,y) != 0, B the characteristic-2 polar form x0y4+x4y0+x1y5+x5y1+x2y6+x6y2 (no x3 term).
Isometries of Q: products of orthogonal transvections t_v(x) = x + (B(x,v)/Q(v)) v, Q(v) != 0 (they preserve Q in
characteristic 2).  Group G of isometries: its orbits on points; an orbit is good iff its own points are pairwise
opposite; two good orbits are compatible iff all cross pairs are opposite (one representative suffices: G preserves B).
The compatibility test uses bit-level arithmetic: B_k(x,y) = x^T M_k y over GF(2), k = 0,1,2 (the three bits of B).
"""
import os

import numpy as np

HEX = '/home/user/degree-diameter/research/d13D7/hex/hex_q8.bin'


def _gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 11
    return r


MUL = np.array([[_gmul(a, b) for b in range(8)] for a in range(8)], dtype=np.int64)
INV = np.zeros(8, dtype=np.int64)
for _a in range(1, 8):
    INV[_a] = int(np.flatnonzero(MUL[_a] == 1)[0])


def load(path=HEX):
    raw = open(path, 'rb').read()
    q, n, L = (int(v) for v in np.frombuffer(raw[:12], dtype=np.int32))
    assert q == 8
    off = 12 + 4 * L * (q + 1)
    lines = np.frombuffer(raw[12:off], dtype=np.int32).reshape(L, q + 1).astype(np.int64)
    P = np.frombuffer(raw[off:off + 7 * n], dtype=np.uint8).reshape(n, 7).astype(np.int64)
    return n, L, lines, P


N, NL, LINES, P = load()
PW = 8 ** np.arange(7, dtype=np.int64)
CODES = P @ PW
assert np.all(np.diff(CODES) > 0)
I7 = np.eye(7, dtype=np.int64)
PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
J = np.zeros((7, 7), np.int64)
for _a, _b in PAIRS:
    J[_a, _b] = 1
NO = 8 ** 9 * 63 * 4095 * 262143          # |O(7,8)| = |Sp(6,8)| = 2^27 3^7 5 7^3 13 19 73
PRIMES = [2, 3, 5, 7, 13, 19, 73]


def bdot(X, Y):
    """B(x,y) over GF(8) for coordinate arrays X, Y (broadcasting over leading axes)."""
    return (MUL[X[..., 0], Y[..., 4]] ^ MUL[X[..., 4], Y[..., 0]] ^ MUL[X[..., 1], Y[..., 5]]
            ^ MUL[X[..., 5], Y[..., 1]] ^ MUL[X[..., 2], Y[..., 6]] ^ MUL[X[..., 6], Y[..., 2]])


def qval(X):
    """Q(x) = x0x4 + x1x5 + x2x6 + x3^2 over GF(8)."""
    return (MUL[X[..., 0], X[..., 4]] ^ MUL[X[..., 1], X[..., 5]] ^ MUL[X[..., 2], X[..., 6]]
            ^ MUL[X[..., 3], X[..., 3]])


def gmm(A, B):
    """matrix product over GF(8)."""
    return np.bitwise_xor.reduce(MUL[A[:, :, None], B[None, :, :]], axis=1)


def mpow(g, e):
    R = I7.copy()
    Bm = g.copy()
    while e:
        if e & 1:
            R = gmm(R, Bm)
        e >>= 1
        if e:
            Bm = gmm(Bm, Bm)
    return R


def order_of(g):
    """exact order of an element g of O(7,8) (its order divides NO)."""
    m = NO
    for pr in PRIMES:
        while m % pr == 0 and np.array_equal(mpow(g, m // pr), I7):
            m //= pr
    return m


def divisors(m):
    divs = [1]
    rest = m
    for pr in PRIMES:
        if rest % pr:
            continue
        e = 0
        while rest % pr == 0:
            rest //= pr
            e += 1
        divs = [d * pr ** k for d in divs for k in range(e + 1)]
    assert rest == 1, 'order has a prime factor outside PRIMES'
    return sorted(divs)


def transvection(v):
    """orthogonal transvection t_v(x) = x + B(x,v)/Q(v) v as a 7x7 matrix over GF(8); needs Q(v) != 0."""
    c = INV[int(qval(v))]
    w = np.zeros(7, np.int64)                  # w_j = coefficient of x_j in B(x, v)
    w[0], w[4], w[1], w[5], w[2], w[6] = v[4], v[0], v[5], v[1], v[6], v[2]
    return I7 ^ MUL[c, MUL[v[:, None], w[None, :]]]


def is_isom(g):
    """g preserves Q (checked on a sample of random points and on the matrix action on the point set)."""
    Y = gmm(P[:2000], g.T)
    return bool(np.array_equal(qval(Y), np.zeros(Y.shape[0], np.int64)))


def rref(M):
    M = M.copy()
    rows, cols = M.shape
    piv = []
    r = 0
    for c in range(cols):
        pr = None
        for i in range(r, rows):
            if M[i, c]:
                pr = i
                break
        if pr is None:
            continue
        M[[r, pr]] = M[[pr, r]]
        M[r] = MUL[INV[M[r, c]], M[r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= MUL[M[i, c], M[r]]
        piv.append(c)
        r += 1
        if r == rows:
            break
    return M, piv


def rank(M):
    return len(rref(M)[1])


def nullspace(M):
    """rows: a basis of {x in GF(8)^cols : M x = 0}."""
    cols = M.shape[1]
    R, piv = rref(M)
    basis = []
    for f in range(cols):
        if f in piv:
            continue
        x = np.zeros(cols, np.int64)
        x[f] = 1
        for i, pc in enumerate(piv):
            x[pc] = R[i, f]          # -R[i,f] = R[i,f] in characteristic 2
        basis.append(x)
    return np.array(basis, dtype=np.int64).reshape(-1, cols)


def gram(E):
    k = E.shape[0]
    G = np.zeros((k, k), np.int64)
    for i in range(k):
        for j in range(k):
            G[i, j] = bdot(E[i], E[j])
    return G


def rand_vec_in(rng, Bm):
    c = rng.integers(0, 8, Bm.shape[0])
    v = np.zeros(7, np.int64)
    for i in range(Bm.shape[0]):
        v ^= MUL[c[i], Bm[i]]
    return v


def rand_transv_in(rng, Bm, L):
    """product of L transvections t_v, v random in the span of the rows of Bm with Q(v) != 0 (acts trivially on the
    B-orthogonal complement of that span)."""
    g = I7.copy()
    for _ in range(L):
        while True:
            v = rand_vec_in(rng, Bm)
            if int(qval(v)) != 0:
                break
        g = gmm(transvection(v), g)
    return g


def random_nondeg(rng, k):
    """rows E: k independent vectors spanning a B-nondegenerate subspace (Gram matrix nonsingular); k even."""
    assert k % 2 == 0
    while True:
        E = rng.integers(0, 8, (k, 7)).astype(np.int64)
        if rank(gram(E)) == k and rank(E) == k:
            return E


def split(rng, k):
    """U (rows of E, nondegenerate, dim k) and U-perp (rows of F, dim 7-k)."""
    E = random_nondeg(rng, k)
    F = nullspace(gmm(E, J))          # x in U-perp  <=>  (E J) x = 0
    return E, F


def perm_of(g):
    """permutation of the point indices induced by x -> g x (renormalised)."""
    Y = gmm(P, g.T)
    lead_idx = (Y != 0).argmax(axis=1)
    lead = Y[np.arange(N), lead_idx]
    Y = MUL[INV[lead][:, None], Y]
    codes = Y @ PW
    idx = np.searchsorted(CODES, codes)
    assert np.array_equal(CODES[np.minimum(idx, N - 1)], codes), 'image is not a point of Q'
    return idx


def orbit_labels(perms):
    lab = np.arange(N)
    while True:
        old = lab.copy()
        for pi in perms:
            vals = lab.copy()
            lab = np.minimum(lab, vals[pi])
            np.minimum.at(lab, pi, vals)
        lab = lab[lab]
        if np.array_equal(lab, old):
            break
    _, lab = np.unique(lab, return_inverse=True)
    return lab.astype(np.int64)


def analyse(lab):
    """orbit sizes, representative (first point) of each orbit, and the good orbits."""
    ncomp = int(lab.max()) + 1
    sizes = np.bincount(lab, minlength=ncomp)
    _, rep = np.unique(lab, return_index=True)
    rep_of = rep[lab]
    b = bdot(P[rep_of], P)                       # B(rep, y) for every point y
    bad_pt = (b == 0) & (np.arange(N) != rep_of)
    bad = np.zeros(ncomp, bool)
    bad[lab[bad_pt]] = True
    good = np.flatnonzero(~bad)
    return sizes, rep, good


def _bitmats():
    Ms = []
    for k in range(3):
        M = np.zeros((21, 21), np.float32)
        for a, b in PAIRS:
            for i in range(3):
                for j in range(3):
                    M[3 * a + i, 3 * b + j] = (int(MUL[1 << i, 1 << j]) >> k) & 1
        Ms.append(M)
    return Ms


MATS = _bitmats()


def bits(X):
    """(n,7) GF(8) coordinates -> (n,21) float32 bit vectors (index 3*coordinate + bit)."""
    return np.stack([(X >> i) & 1 for i in range(3)], axis=-1).reshape(X.shape[0], 21).astype(np.float32)


def compat_packed(lab, rep, good, blk=128):
    """packed compatibility rows (K x W uint64): bit j of row k set iff good orbits k and j are compatible.
    B_k(r, y) for the three bits k of B(r, y): S = [Y M_0^T; Y M_1^T; Y M_2^T] R^T, zero iff all three bits vanish."""
    K = good.size
    ncomp = rep.size
    pos = np.full(ncomp, -1, np.int64)
    pos[good] = np.arange(K)
    pts = np.flatnonzero(pos[lab] >= 0)
    pl = pos[lab[pts]]
    o = np.argsort(pl, kind='stable')
    pts = pts[o]
    pl = pl[o]
    starts = np.searchsorted(pl, np.arange(K))
    YB = bits(P[pts])
    M = YB.shape[0]
    YM = np.vstack([YB @ Mk.T for Mk in MATS])        # (3M, 21)
    RB = bits(P[rep[good]])
    W = (K + 63) // 64
    out = np.zeros((K, W), np.uint64)
    for s in range(0, K, blk):
        e = min(K, s + blk)
        S = (YM @ RB[s:e].T).reshape(3, M, e - s).astype(np.int32) & 1
        zero = (S[0] | S[1] | S[2]) == 0                # B(r, y) = 0 (zero points of the block)
        anyzero = np.logical_or.reduceat(zero, starts, axis=0)   # orbit j has a point NOT opposite to rep r
        comp = ~anyzero                                 # so orbit j is compatible with r iff no such point
        full = np.zeros((K, 2 * 64), bool)
        full[:, :e - s] = comp
        words = np.packbits(full, axis=1, bitorder='little').view('<u8')
        w0 = s // 64
        nw = min(words.shape[1], W - w0)
        out[:, w0:w0 + nw] = words[:, :nw]
    return out


def write_graph_packed(path, rows, w):
    """binary graph for wclq2: int32 K, int32 W, int32 w[K], uint64 rows[K*W]."""
    K, W = rows.shape
    with open(path, 'wb') as f:
        np.array([K, W], '<i4').tofile(f)
        np.asarray(w, '<i4').tofile(f)
        np.ascontiguousarray(rows, dtype='<u8').tofile(f)


def packed_density(rows):
    K = rows.shape[0]
    pc = np.unpackbits(rows.view(np.uint8), bitorder='little').sum()
    return float(pc) / max(1, K * (K - 1))


def read_clique(path):
    with open(path) as f:
        head = f.readline().split()
        verts = [int(line) for line in f if line.strip()]
    return int(head[1]), bool(int(head[3])), verts


def pairwise_ok(idx):
    idx = np.asarray(idx, dtype=np.int64)
    if len(set(idx.tolist())) != len(idx):
        return False
    X = P[idx]
    G = bdot(X[:, None, :], X[None, :, :])
    np.fill_diagonal(G, 1)
    return bool(np.all(G != 0))


def fingerprint(sizes, good):
    isg = np.zeros(sizes.size, bool)
    isg[good] = True
    key = {}
    for s, g in zip(sizes.tolist(), isg.tolist()):
        key[(s, g)] = key.get((s, g), 0) + 1
    return ';'.join(f'{s}{"g" if g else "b"}:{c}' for (s, g), c in sorted(key.items()))


def mat_to_text(M):
    return '\n'.join(' '.join(str(int(x)) for x in row) for row in M) + '\n'


def read_gens(path):
    desc, blocks = '', []
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.startswith('#'):
            desc = line[1:].strip()
        elif line.strip() and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return desc, [np.array(b, dtype=np.int64) for b in blocks]
