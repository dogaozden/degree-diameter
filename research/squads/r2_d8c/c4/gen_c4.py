"""gen_c4.py (own-d8-compound round 2, card c4): pencil-coordinate Z_m lift of I(H(q)) with the second matching
p -- P^k(p) for an odd power k of the duality P = phi (k = 1: 'same', k = -1: 'inv', k = 3, -3, ...).
Matching 1: p -- P(p) with voltage f1(p) = A1 + s1*c(p);  matching 2: p -- P^k(p) with voltage f2(p) = A2 + s2*c(p).
c(p) is the pencil coordinate of pencil_dual.py (same axis, same seed convention).
Hexagon voltages 0.  The hexagon part of the file is written once (hexpart), so each config costs only the matchings.

Usage (library): build(q, phi, m, seed, k, A1, s1, A2, s2) -> writes text to a stream; see sweep.py.
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load


def perm_power(P, k):
    """P: permutation array on 2N; return the array of P^k (k may be negative)."""
    if k < 0:
        inv = np.empty_like(P)
        inv[P] = np.arange(P.shape[0])
        P = inv
        k = -k
    out = np.arange(P.shape[0])
    base = P.copy()
    while k:
        if k & 1:
            out = base[out]
        base = base[base]
        k >>= 1
    return out


def gf_tables(q):
    """GF(q) tables in the encoding of hexgen2.c."""
    polys = {4: ([1, 1], 2), 8: ([1, 1, 0], 3), 9: ([1, 0], 2), 16: ([1, 1, 0, 0], 4), 25: ([2, 0], 2),
             27: ([1, 2, 0], 3), 32: ([1, 0, 1, 0, 0], 5)}
    p = next(d for d in range(2, q + 1) if q % d == 0)
    cfs, e = polys.get(q, ([0], 1))
    def dig(x):
        out = []
        for _ in range(e):
            out.append(x % p); x //= p
        return out
    def enc(v):
        s, pw = 0, 1
        for d in v:
            s += d * pw; pw *= p
        return s
    ADD = [[enc([(u + v) % p for u, v in zip(dig(x), dig(y))]) for y in range(q)] for x in range(q)]
    MUL = [[0] * q for _ in range(q)]
    for x in range(q):
        for y in range(q):
            a, b = dig(x), dig(y)
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                f = r[k]
                if not f:
                    continue
                r[k] = 0
                for i in range(e):
                    r[k - e + i] = (r[k - e + i] - f * cfs[i]) % p
            MUL[x][y] = enc(r[:e])
    NEG = [next(y for y in range(q) if ADD[x][y] == 0) for x in range(q)]
    INV = [0] + [next(y for y in range(q) if MUL[x][y] == 1) for x in range(1, q)]
    return ADD, MUL, NEG, INV


def pencil_coords(q, coord, seed):
    """pencil coordinate c(p) in 0..q (q = infinity), axis points get a random value; same as pencil_dual.py."""
    C = coord.astype(np.int64)
    N = C.shape[0]
    rng = np.random.default_rng(seed)
    ADD, MUL, NEG, INV = gf_tables(q)
    a = rng.integers(0, q, 7)
    a2 = rng.integers(0, q, 7)
    PAIRS = [(0, 4), (4, 0), (1, 5), (5, 1), (2, 6), (6, 2)]
    two = ADD[1][1]

    def bform(x, y):
        acc = 0
        for i, j in PAIRS:
            acc = ADD[acc][MUL[x[i]][y[j]]]
        return ADD[acc][NEG[MUL[two][MUL[x[3]][y[3]]]]]
    c = np.empty(N, dtype=np.int64)
    for p in range(N):
        s_, t_ = bform(C[p], a), bform(C[p], a2)
        if t_ != 0:
            c[p] = MUL[s_][INV[t_]]
        elif s_ != 0:
            c[p] = q
        else:
            c[p] = -1
    spec = rng.integers(0, q + 1, N)
    return np.where(c < 0, spec, c)


def setup(q, phif, seed):
    N, LP, PL, coord = load(q)
    phi = np.fromfile(phif, dtype=np.int32).astype(np.int64)
    assert phi.shape[0] == 2 * N
    c = pencil_coords(q, coord, seed)
    return N, LP, phi, c


def hexpart(N, LP):
    lines = []
    for l in range(N):
        for p in LP[l]:
            lines.append(f'{p} {N + l} 0')
    return '\n'.join(lines) + '\n'


def write_base(fh, N, m, hexpart_text, phi, c, k, A1, s1, A2, s2, q):
    """Write the full lift file for Z m to file object fh."""
    fh.write(f'Z {m}\n{2 * N}\n')
    fh.write(' '.join(['0'] * N + ['1'] * N) + '\n')
    fh.write(hexpart_text)
    f1 = (A1 + s1 * c) % m
    f2 = (A2 + s2 * c) % m
    P = phi                       # permutation of 0..2N-1 (points <-> lines)
    Pk = perm_power(P, k)
    pts = np.arange(N)
    lines_m1 = [f'{p} {P[p]} {f1[p]}' for p in pts]
    lines_m2 = [f'{p} {Pk[p]} {f2[p]}' for p in pts]
    fh.write('\n'.join(lines_m1) + '\n')
    fh.write('\n'.join(lines_m2) + '\n')
