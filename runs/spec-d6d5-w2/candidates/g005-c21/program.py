import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence (D >= 3) and Araujo-Pardo-Lopez (D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) with q = d - 1 when that is a prime power (degree d, diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: bipartite double covers of Cayley graphs.
#
# For a group G of order m with a symmetric generating set S (|S| = d, inverse-closed),
# the bipartite double cover has vertices (g, c) for c in {0, 1} and edges
# (g, 0)-(g*s, 1) for s in S. It is d-regular, bipartite, with 2m vertices.
#
# Left multiplication and the side flip (g,c) -> (g,1-c) are automorphisms, so the
# diameter is at most D iff a BFS from (e, 0) reaches all 2m vertices within D steps.
# This makes each evaluation a single cheap BFS.
# ----------------------------------------------------------------------------

def _sample_group(order, rng):
    """Random semidirect product Z_m x| Z_k of total order `order`, or None."""
    ks = [k for k in range(1, 13) if order % k == 0 and order // k >= 2]
    if not ks:
        return None
    for _ in range(40):
        k = rng.choice(ks)
        m1 = order // k
        if k == 1:
            r = 1
        else:
            cands = [r for r in range(1, m1)
                     if math.gcd(r, m1) == 1 and pow(r, k, m1) == 1 % m1]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            total, mul, inv = lib.semidirect_group(m1, k, r)
        except ValueError:
            continue
        return total, mul, inv
    return None


def _rand_block(m, inv, rng, used, size):
    """A symmetric block of generators: (x, x^-1) for size 2, (x,) for an involution (size 1)."""
    for _ in range(60):
        x = rng.randrange(1, m)
        if x in used:
            continue
        y = inv(x)
        if size == 1:
            if y == x:
                return (x,)
        elif y != x and y not in used:
            return (x, y)
    return None


def _rand_blocks(m, inv, d, rng):
    """Random inverse-closed generating set of size exactly d, as a list of blocks."""
    for _ in range(100):
        blocks = []
        used = {0}
        total = 0
        ok = True
        while total < d:
            rem = d - total
            if rem == 1:
                size = 1
            else:
                size = 1 if rng.random() < 0.15 else 2
            b = _rand_block(m, inv, rng, used, size)
            if b is None:
                ok = False
                break
            blocks.append(b)
            used.update(b)
            total += len(b)
        if ok:
            return blocks
    return None


def _flat(blocks):
    return [s for b in blocks for s in b]


class _PermCache:
    """Caches right-multiplication permutations g -> g*s."""

    def __init__(self, m, mul):
        self.m = m
        self.mul = mul
        self.cache = {}

    def get(self, s):
        p = self.cache.get(s)
        if p is None:
            mul, m = self.mul, self.m
            p = [mul(g, s) for g in range(m)]
            self.cache[s] = p
        return p


def _cost(m, pc, S, D):
    """Number of vertices of the double cover not reached from (e, 0) within D steps. Zero means valid."""
    perms = [pc.get(s) for s in S]
    seen = bytearray(2 * m)
    seen[0] = 1
    frontier = [0]
    count = 1
    for _ in range(D):
        nxt = []
        for x in frontier:
            g = x >> 1
            nc = (x & 1) ^ 1
            for p in perms:
                y = (p[g] << 1) | nc
                if not seen[y]:
                    seen[y] = 1
                    nxt.append(y)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * m - count


def _search_group(m, d, D, mul, inv, rng, deadline, steps):
    """Hill-climb an inverse-closed generating set of size d so the double cover has diameter <= D."""
    pc = _PermCache(m, mul)
    blocks = _rand_blocks(m, inv, d, rng)
    if blocks is None:
        return None
    cur = _cost(m, pc, _flat(blocks), D)
    for _ in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        bi = rng.randrange(len(blocks))
        used = {0}
        for j, b in enumerate(blocks):
            if j != bi:
                used.update(b)
        nb = _rand_block(m, inv, rng, used, len(blocks[bi]))
        if nb is None:
            continue
        cand = blocks[:bi] + [nb] + blocks[bi + 1:]
        c2 = _cost(m, pc, _flat(cand), D)
        if c2 <= cur or rng.random() < 0.02:
            blocks, cur = cand, c2
    return _flat(blocks) if cur == 0 else None


def _cover_edges(m, mul, S):
    """Edges of the bipartite double cover: A vertex g to B vertex m + g*s for s in S."""
    E = []
    for g in range(m):
        for s in S:
            E.append((g, m + mul(g, s)))
    return 2 * m, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    # D >= 3: projective plane and Araujo-Pardo-Lopez graphs both have diameter 3.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    ar = _araujo(d)
    if ar is not None:
        consider(ar[0], ar[1])

    if D == 3:
        return best_n, best_e

    # D >= 4: new search over bipartite double covers of Cayley graphs.
    moore = lib.moore_bound(d, D)
    m0 = max(best_n // 2 + 1, int(0.4 * moore / 2))
    fails = 0
    while time.monotonic() < deadline:
        lo_half = best_n // 2 + 1
        if m0 < lo_half:
            m0 = lo_half
        m = m0 + rng.randrange(4)
        g = _sample_group(m, rng)
        if g is None:
            fails += 1
        else:
            order, mul, inv = g
            S = _search_group(order, d, D, mul, inv, rng, deadline, 400)
            if S is None:
                fails += 1
            else:
                n_c, E = _cover_edges(order, mul, S)
                consider(n_c, E)
                m0 = max(m0, order + 1)
                fails = 0
        if fails > 40:
            fails = 0
            m0 = max(lo_half, m0 - 2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
