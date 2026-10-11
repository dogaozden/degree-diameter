import math
import random
import time
from itertools import permutations

import lib


# ----------------------------------------------------------------------------
# Finite groups as multiplication tables: (n, tab, e) with elements 0..n-1,
# tab[a][b] = a*b, and e the identity index.
# ----------------------------------------------------------------------------

def _cyc(m):
    tab = [[(a + b) % m for b in range(m)] for a in range(m)]
    return m, tab, 0


def _semi(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    tab = [[mul(a, b) for b in range(order)] for a in range(order)]
    return order, tab, 0


def _gen_dih(m1, m2):
    """Generalized dihedral group of the abelian group Z_m1 x Z_m2 (inversion action)."""
    a = m1 * m2

    def add_a(p, q):
        return (((p // m2) + (q // m2)) % m1) * m2 + ((p % m2) + (q % m2)) % m2

    def neg_a(p):
        return ((-(p // m2)) % m1) * m2 + ((-(p % m2)) % m2)

    neg = [neg_a(p) for p in range(a)]
    n = 2 * a
    tab = [[0] * n for _ in range(n)]
    for i in range(n):
        p, s = i % a, i // a
        row = tab[i]
        for j in range(n):
            q, t = j % a, j // a
            qq = q if s == 0 else neg[q]
            row[j] = add_a(p, qq) + ((s + t) % 2) * a
    return n, tab, 0


def _wreath(a, b):
    """Z_a wr Z_b = (Z_a^b) semidirect Z_b with cyclic shift."""
    m = a ** b
    n = m * b

    def dec(v):
        return [(v // a ** i) % a for i in range(b)]

    def enc(c):
        return sum(c[i] * a ** i for i in range(b))

    decs = [dec(v) for v in range(m)]
    addv = [[enc([(decs[v][i] + decs[w][i]) % a for i in range(b)]) for w in range(m)]
            for v in range(m)]
    rotv = [[enc([decs[w][(i - t) % b] for i in range(b)]) for w in range(m)]
            for t in range(b)]
    tab = [[0] * n for _ in range(n)]
    for i in range(n):
        v, t = i % m, i // m
        row = tab[i]
        for j in range(n):
            w, s = j % m, j // m
            row[j] = ((t + s) % b) * m + addv[v][rotv[t][w]]
    return n, tab, 0


def _is_even(p):
    inv = 0
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]:
                inv += 1
    return inv % 2 == 0


def _sym(k, even):
    perms = [p for p in permutations(range(k)) if (not even) or _is_even(p)]
    idx = {p: i for i, p in enumerate(perms)}
    n = len(perms)
    tab = [[idx[tuple(p[q[i]] for i in range(k))] for q in perms] for p in perms]
    return n, tab, idx[tuple(range(k))]


def _direct(h1, h2):
    n1, t1, e1 = h1
    n2, t2, e2 = h2
    n = n1 * n2
    tab = [[0] * n for _ in range(n)]
    for i in range(n):
        i1, i2 = divmod(i, n2)
        row = tab[i]
        for j in range(n):
            j1, j2 = divmod(j, n2)
            row[j] = t1[i1][j1] * n2 + t2[i2][j2]
    return n, tab, e1 * n2 + e2


_SMALL = [
    (6, lambda: _gen_dih(3, 1)),
    (8, lambda: _gen_dih(4, 1)),
    (10, lambda: _gen_dih(5, 1)),
    (12, lambda: _sym(4, True)),
    (12, lambda: _gen_dih(6, 1)),
    (14, lambda: _gen_dih(7, 1)),
    (16, lambda: _gen_dih(8, 1)),
    (18, lambda: _gen_dih(9, 1)),
    (24, lambda: _sym(4, False)),
]


def _catalogue(N, rng):
    """Builders for groups of order N (cyclic, dihedral-type, semidirect, products, wreath)."""
    out = [lambda: _cyc(N)]
    if N % 2 == 0 and N >= 6:
        out.append(lambda: _gen_dih(N // 2, 1))
    if N % 4 == 0 and N >= 8:
        out.append(lambda: _gen_dih(2, N // 4))
    for k in range(2, min(N, 13) + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            out.append(lambda m=m, k=k, r=r: _semi(m, k, r))
    for order, builder in _SMALL:
        if N % order == 0 and N // order >= 2:
            kk = N // order
            out.append(lambda builder=builder, kk=kk: _direct(builder(), _cyc(kk)))
    for a, b in ((3, 3), (7, 2), (2, 3), (3, 2), (4, 2), (5, 2), (6, 2)):
        if a ** b * b == N:
            out.append(lambda a=a, b=b: _wreath(a, b))
    return out


def _inverse(n, tab, e):
    inv = [0] * n
    for x in range(n):
        row = tab[x]
        for y in range(n):
            if row[y] == e:
                inv[x] = y
                break
    return inv


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs: A_x ~ B_y iff x^{-1} y in S, |S| = d.
# Left translation is an automorphism, so only the eccentricities of A_e and B_e
# matter: two BFS runs give the full diameter test.
# ----------------------------------------------------------------------------

def _cost(n, tab, e, inv, S, D):
    """Number of vertices not reached within D from A_e and from B_e. Zero iff diameter <= D."""
    invS = [inv[s] for s in S]
    n2 = 2 * n
    total = 0
    for src in (e, n + e):
        seen = bytearray(n2)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < n:
                    row = tab[u]
                    cand = [n + row[s] for s in S]
                else:
                    row = tab[u - n]
                    cand = [row[s] for s in invS]
                for v in cand:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n2 - count
    return total


def _search(n, tab, e, d, D, rng, deadline, iters):
    """Annealed search for a connection set S of size d with diameter <= D."""
    inv = _inverse(n, tab, e)
    S = rng.sample(range(n), d)
    c = _cost(n, tab, e, inv, S, D)
    t0, t1 = 2.0, 0.1
    for it in range(iters):
        if c == 0 or ((it & 31) == 0 and time.monotonic() > deadline):
            break
        temp = t0 * (t1 / t0) ** (it / max(1, iters))
        i = rng.randrange(d)
        s_new = rng.randrange(n)
        if s_new in S:
            continue
        old = S[i]
        S[i] = s_new
        c2 = _cost(n, tab, e, inv, S, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[i] = old
    return list(S) if c == 0 else None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3: projective plane incidence graph when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    # Haar-type search over groups of order N; a graph on 2N vertices.
    hi = min(lib._moore_bound(d, D) // 2, 300)

    while time.monotonic() < deadline:
        lo = max(d, best[0] // 2 + 1)
        if lo > hi:
            break
        if rng.random() < 0.6:
            N = rng.randint(max(lo, hi - 12), hi)
        else:
            N = rng.randint(lo, hi)
        cands = _catalogue(N, rng)
        if not cands:
            continue
        n, tab, e = rng.choice(cands)()
        if n < d:
            continue
        S = _search(n, tab, e, d, D, rng, deadline, 2000)
        if S is not None:
            edges = [(x, n + tab[x][s]) for x in range(n) for s in S]
            consider(2 * n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
