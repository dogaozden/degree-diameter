#!/usr/bin/env python3
"""orbq.py (card c3, squad round 4): orbit unions for pairwise-opposite point sets of H(q), q prime (q = 5, 7).

Port of research/squads/d13D7_r3/c3/orbl.py (which was hard-wired to q = 11).  Points of H(q) = points of Q(6,q) =
{x in PG(6,q): x0x4 + x1x5 + x2x6 - x3^2 = 0}; x, y are opposite iff B(x,y) = x^T J y != 0 (mod q).  Isometries of B
permute the points and preserve opposition, so the G-orbits of any group G < O(7,q) are the building blocks.
Every constant of orbl.py that was 11 is q here (inverse table, |O(7,q)|, its prime divisors, the file name).
Call setq(q) once after import; the functions below then use the module globals.
"""
import os

import numpy as np

HEX_DIR = '/home/user/degree-diameter/research/d13D7/hex'
p = None
N = None
P = None            # N x 7 int64 point coordinates, first nonzero coordinate 1, sorted by code
CODES = None
PW = None
J = None
PJ = None           # row i = (J x_i)^T, so PJ @ y = B(x_i, y)
INV = None
NO = None           # |O(7,q)| = 2 q^9 (q^2-1)(q^4-1)(q^6-1)
PRIMES = None       # primes dividing NO
I7 = np.eye(7, dtype=np.int64)


def prime_factors(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def setq(q):
    global p, N, P, CODES, PW, J, PJ, INV, NO, PRIMES
    p = q
    raw = open(os.path.join(HEX_DIR, f'hex_q{q}.bin'), 'rb').read()
    qq, n, L = (int(v) for v in np.frombuffer(raw[:12], dtype=np.int32))
    assert qq == q, 'hex file has q = %d' % qq
    N = n
    off = 12 + 4 * L * (q + 1)
    P = np.frombuffer(raw[off:off + 7 * N], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    PW = p ** np.arange(7, dtype=np.int64)
    CODES = P @ PW
    assert np.all(np.diff(CODES) > 0)
    J = np.zeros((7, 7), np.int64)
    J[0, 4] = J[4, 0] = J[1, 5] = J[5, 1] = J[2, 6] = J[6, 2] = 1
    J[3, 3] = p - 2
    PJ = (P @ J) % p
    INV = np.array([0] + [pow(x, p - 2, p) for x in range(1, p)], np.int64)
    NO = 2 * p ** 9 * (p ** 2 - 1) * (p ** 4 - 1) * (p ** 6 - 1)
    PRIMES = prime_factors(NO)


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


def divisors(m):
    """all divisors of m (m divides NO, so its prime factors lie in PRIMES)."""
    divs = [1]
    for pr in PRIMES:
        if m % pr:
            continue
        e = 0
        while m % pr == 0:
            m //= pr
            e += 1
        divs = [d * pr ** k for d in divs for k in range(e + 1)]
    assert m == 1
    return sorted(divs)


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
    """U = random non-degenerate k-dim subspace (rows of E), U-perp (rows of F)."""
    E = random_nondeg_subspace(rng, k)
    F = nullspace_mod((E @ J) % p)
    return E, F


def rand_refl_in(rng, Bm, L):
    """product of L reflections in random non-singular vectors of the span of the rows of Bm (acts trivially on the
    B-orthogonal complement of that span)."""
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
    b = (PJ[rep_of] * P).sum(axis=1) % p
    bad_pt = (b == 0) & (np.arange(N) != rep_of)
    bad = np.zeros(ncomp, bool)
    bad[lab[bad_pt]] = True
    good = np.flatnonzero(~bad)
    return sizes, rep, good


def compat_packed(lab, rep, good):
    """packed compatibility rows (K x W uint64): bit j of row k set iff good orbits k and j are compatible (every
    cross pair opposite).  Computed 64 columns at a time."""
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
    PJs = PJ[pts].astype(np.float32)
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
    """cheap invariant of the orbit structure (sizes of all orbits, with goodness)."""
    isg = np.zeros(sizes.size, bool)
    isg[good] = True
    key = {}
    for s, g in zip(sizes.tolist(), isg.tolist()):
        key[(s, g)] = key.get((s, g), 0) + 1
    return ';'.join(f'{s}{"g" if g else "b"}:{c}' for (s, g), c in sorted(key.items()))


def mat_to_text(M):
    return '\n'.join(' '.join(str(int(x)) for x in row) for row in M) + '\n'


def read_gens(path):
    """(description, [7x7 matrices]) from a gens file: '# description', then '# generator i' blocks."""
    desc, blocks = '', []
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.startswith('#'):
            desc = line[1:].strip()
        elif line.strip() and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return desc, [np.array(b, dtype=np.int64) for b in blocks]
