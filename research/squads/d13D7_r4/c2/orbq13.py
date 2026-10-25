#!/usr/bin/env python3
"""Card c2 (squad round 4, job cell-13-7): orbit unions of subgroups of O(7,13) acting on the points of H(13).

Port of research/squads/d13D7_r3/c3/orbl.py (which was written for q = 11) to q = 13.  Everything that depended on
p = 11 is generic now: the inverse table, the group order |O(7,13)| and its prime list, the float reduction in the
compatibility test.  Points: the 402,234 points of Q(6,13) (= points of H(13)), hexagon file hex_q13.bin, coordinates only.

A point set S is pairwise opposite iff B(x,y) != 0 for x != y in S, B(x,y) = x^T J y.  For a group G of isometries of
B, the G-orbits are the building blocks: an orbit is "good" iff its own points are pairwise opposite; two good orbits
O_k, O_j are compatible iff B(rep_k, y) != 0 for all y in O_j.  A union of pairwise compatible good orbits is pairwise
opposite; the weight of an orbit is its size.
"""
import os

import numpy as np

HEX = '/home/user/degree-diameter/research/d13D7/hex/hex_q13.bin'
p = 13
Q = 13


def load_coords(path=HEX):
    with open(path, 'rb') as f:
        hdr = np.frombuffer(f.read(12), dtype=np.int32)
        q, N, L = int(hdr[0]), int(hdr[1]), int(hdr[2])
        assert q == p
        f.seek(12 + 4 * L * (q + 1))
        coord = np.frombuffer(f.read(7 * N), dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return coord


P = load_coords()
N = P.shape[0]
J = np.zeros((7, 7), np.int64)
J[0, 4] = J[4, 0] = J[1, 5] = J[5, 1] = J[2, 6] = J[6, 2] = 1
J[3, 3] = p - 2
I7 = np.eye(7, dtype=np.int64)
PW = p ** np.arange(7, dtype=np.int64)
CODES = P @ PW
assert np.all(np.diff(CODES) > 0)
INV = np.array([0] + [pow(i, p - 2, p) for i in range(1, p)], np.int64)
PJ = (P @ J) % p                                    # row i = (J x_i)^T, so PJ @ y = B(x_i, y)
NO = 2 * p ** 9 * (p ** 2 - 1) * (p ** 4 - 1) * (p ** 6 - 1)   # |O(7,13)|
PRIMES = [2, 3, 5, 7, 13, 17, 61, 157]              # the primes dividing |O(7,13)| (checked: product is NO)
_r = NO
for _pr in PRIMES:
    while _r % _pr == 0:
        _r //= _pr
assert _r == 1, 'NO has a prime factor outside PRIMES'


def mmul(a, b):
    return (a @ b) % p


def mpow(g, e):
    R = I7.copy()
    B = g.copy()
    while e:
        if e & 1:
            R = mmul(R, B)
        B = mmul(B, B)
        e >>= 1
    return R


def order_of(g):
    """exact order of an isometry g (its order divides NO)."""
    m = NO
    for pr in PRIMES:
        while m % pr == 0 and np.array_equal(mpow(g, m // pr), I7):
            m //= pr
    return m


def is_isom(g):
    return np.array_equal(mmul(mmul(g.T, J), g), J % p)


def refl(v):
    """reflection x -> x - 2 B(x,v)/B(v,v) v (B(v,v) != 0)."""
    c = int(v @ J @ v) % p
    cinv = pow(c, p - 2, p)
    return (I7 - 2 * cinv * np.outer(v, (J @ v) % p)) % p


def rand_isom(rng, k):
    """product of k reflections in random non-singular vectors (a random isometry)."""
    g = I7.copy()
    for _ in range(k):
        while True:
            v = rng.integers(0, p, 7)
            if int(v @ J @ v) % p:
                break
        g = mmul(refl(v), g)
    return g


def random_nondeg_subspace(rng, k):
    """rows of E: a basis of a non-degenerate k-dim subspace U (Gram matrix invertible)."""
    E = []
    while len(E) < k:
        v = rng.integers(0, p, 7).astype(np.int64)
        for e in E:
            ee = int(e @ J @ e) % p
            v = (v - (int(v @ J @ e) % p) * pow(ee, p - 2, p) * e) % p
        if int(v @ J @ v) % p:
            E.append(v)
    return np.array(E, dtype=np.int64)


def nullspace_mod(M):
    """basis (rows) of {x in F_p^7 : M x = 0}."""
    M = M.copy() % p
    rows, cols = M.shape
    piv = []
    r = 0
    for c in range(cols):
        pr = None
        for i in range(r, rows):
            if M[i, c] % p:
                pr = i
                break
        if pr is None:
            continue
        M[[r, pr]] = M[[pr, r]]
        M[r] = (M[r] * pow(int(M[r, c]), p - 2, p)) % p
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] = (M[i] - M[i, c] * M[r]) % p
        piv.append(c)
        r += 1
        if r == rows:
            break
    basis = []
    for f in [c for c in range(cols) if c not in piv]:
        x = np.zeros(cols, np.int64)
        x[f] = 1
        for i, pc in enumerate(piv):
            x[pc] = (-M[i, f]) % p
        basis.append(x)
    return np.array(basis, dtype=np.int64)


def split(rng, k):
    """U = random non-degenerate k-dim subspace (rows of E) and U-perp (rows of F): V = U + U-perp orthogonal."""
    E = random_nondeg_subspace(rng, k)
    F = nullspace_mod((E @ J) % p)
    return E, F


def rand_refl_in(rng, Bm, L):
    """product of L reflections in random non-singular vectors of the span of the rows of Bm.  Such a product acts
    trivially on the B-orthogonal complement of that span."""
    g = I7.copy()
    for _ in range(L):
        while True:
            c = rng.integers(0, p, Bm.shape[0])
            v = (c @ Bm) % p
            if int(v @ J @ v) % p:
                break
        g = mmul(refl(v), g)
    return g


def perm_of(g):
    """permutation of the point indices induced by x -> g x (renormalised)."""
    Y = (P @ g.T) % p
    lead_idx = (Y != 0).argmax(axis=1)
    lead = Y[np.arange(N), lead_idx]
    Y = (Y * INV[lead][:, None]) % p
    codes = Y @ PW
    idx = np.searchsorted(CODES, codes)
    assert np.array_equal(CODES[idx], codes), 'image is not a point of Q'
    return idx


def orbit_labels(perms):
    """labels 0..n-1 of the orbits of the group generated by the permutations (min-label propagation)."""
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
    b = (PJ[rep_of] * P).sum(axis=1) % p            # B(rep, y) for every point y
    bad_pt = (b == 0) & (np.arange(N) != rep_of)    # y in the orbit of rep, y != rep, B(rep, y) = 0
    bad = np.zeros(ncomp, bool)
    bad[lab[bad_pt]] = True
    good = np.flatnonzero(~bad)
    return sizes, rep, good


def compat_packed(lab, rep, good):
    """packed compatibility rows (K x W uint64, bit j of row k set iff good orbits k and j are compatible), computed
    one 64-column block at a time.  The diagonal is clear automatically: a representative is orthogonal to itself."""
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
    PJs = PJ[pts].astype(np.float32)                # entries < 13; sums of 7 products < 2^24: exact in float32
    reps = P[rep[good]].astype(np.float32)
    W = (K + 63) // 64
    out = np.zeros((K, W), np.uint64)
    for b in range(W):
        s, e = 64 * b, min(K, 64 * b + 64)
        M = PJs @ reps[s:e].T
        Z = (np.fmod(M, float(p)) == 0).astype(np.float32)
        C = np.add.reduceat(Z, starts, axis=0)
        blk = np.zeros((K, 64), bool)
        blk[:, :e - s] = (C == 0)
        out[:, b] = np.packbits(blk, axis=1, bitorder='little').view('<u8')[:, 0]
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
    """(weight, optimal flag, vertex list) from a wclq2 output file."""
    with open(path) as f:
        head = f.readline().split()
        verts = [int(line) for line in f if line.strip()]
    return int(head[1]), bool(int(head[3])), verts


def pairwise_ok(idx):
    idx = np.asarray(idx, dtype=np.int64)
    if len(set(idx.tolist())) != len(idx):
        return False
    X = P[idx]
    G = (X @ J @ X.T) % p
    np.fill_diagonal(G, 1)
    return bool(np.all(G != 0))


def fingerprint(sizes, good):
    """cheap invariant of the orbit structure (sizes of all orbits, with goodness): used to skip repeated groups."""
    isg = np.zeros(sizes.size, bool)
    isg[good] = True
    key = {}
    for s, g in zip(sizes.tolist(), isg.tolist()):
        key[(s, g)] = key.get((s, g), 0) + 1
    return ';'.join(f'{s}{"g" if g else "b"}:{c}' for (s, g), c in sorted(key.items()))


def mat_to_text(M):
    return '\n'.join(' '.join(str(int(x)) for x in row) for row in M) + '\n'


def text_to_mat(s):
    rows = [list(map(int, line.split())) for line in s.strip().splitlines() if line.strip()]
    return np.array(rows, dtype=np.int64)


def divisors_from_factor(m):
    """all divisors of m (m must divide |O(7,13)|, so its prime factors lie in PRIMES)."""
    divs = [1]
    for pr in PRIMES:
        if m % pr:
            continue
        e = 0
        while m % pr == 0:
            m //= pr
            e += 1
        divs = [d * pr ** k for d in divs for k in range(e + 1)]
    assert m == 1, 'order has a prime factor outside PRIMES'
    return sorted(divs)
