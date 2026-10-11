import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback families: projective plane incidence and Araujo-Pardo-Lopez (D = 3),
# plus K_{d,d} (diameter 2), which is always valid for D >= 2.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite Haar-type graphs over a finite group G.
#
# Vertices A_g = g and B_h = m + h, for g, h in G with |G| = m.
# Connection set S (|S| = d) gives edges A_g -- B_{g*s} for s in S.
# This is simple, bipartite and d-regular. Left multiplication by G is an
# automorphism acting transitively on each side, so the diameter is <= D iff
# BFS from A_e and from B_e reaches everything within D steps.
#
# Groups used: cyclic Z_m, affine AGL(1,p) (order p(p-1)), and PSL/PGL(2,q)
# for small prime powers q. Orders near 2*(record/2) are the targets; the
# search climbs from the current best order.
# ----------------------------------------------------------------------------

def _is_prime(p):
    return p >= 2 and all(p % k for k in range(2, int(p ** 0.5) + 1))


def _affine(p):
    """AGL(1, p): maps x -> a x + b, a != 0; element (a, b) encoded as (a-1)*p + b."""
    m = p * (p - 1)

    def mul(i, j):
        a, b = i // p + 1, i % p
        c, e = j // p + 1, j % p
        return ((a * c) % p - 1) * p + (a * e + b) % p

    return m, 0, mul


def _matrix_group(q, special):
    """PSL(2,q) if special else PGL(2,q), as canonical 2x2 matrices modulo scalars."""
    F = lib.GF(q)
    mt = F.mul_table.tolist()
    at = F.add_table.tolist()
    ng = F._neg.tolist()
    invl = [0] + [F.inv(a) for a in range(1, q)]

    def canon(x):
        if special:
            return min(x, tuple(ng[v] for v in x))
        k = next(i for i in range(4) if x[i])
        c = invl[x[k]]
        return tuple(mt[c][v] for v in x)

    elems = set()
    for x in itertools.product(range(q), repeat=4):
        a, b, c, e = x
        dt = at[mt[a][e]][ng[mt[b][c]]]
        if (dt == 1) if special else (dt != 0):
            elems.add(canon(x))
    elems = sorted(elems)
    idx = {x: i for i, x in enumerate(elems)}

    def mul(i, j):
        a, b, c, e = elems[i]
        p, r, s, t = elems[j]
        y = (at[mt[a][p]][mt[b][s]], at[mt[a][r]][mt[b][t]],
             at[mt[c][p]][mt[e][s]], at[mt[c][r]][mt[e][t]])
        return idx[canon(y)]

    ident = idx[canon((1, 0, 0, 1))]
    return len(elems), ident, mul


def _group_specs(lo, hi):
    """Specs (order, spec) of non-cyclic groups with order in [lo, hi], sorted by order."""
    out = []
    p = 3
    while p * (p - 1) <= hi:
        if _is_prime(p) and lo <= p * (p - 1) <= hi:
            out.append((p * (p - 1), ('aff', p)))
        p += 1
    for q in (5, 7, 8, 9, 11):
        if not lib.is_prime_power(q):
            continue
        base = q * (q * q - 1)
        for special in (True, False):
            if not special and q % 2 == 0:
                continue  # PSL = PGL for even q
            order = base // 2 if (special and q % 2) else base
            if lo <= order <= hi:
                out.append((order, ('mat', q, special)))
    out.sort()
    return out


def _build_group(spec):
    """Return (m, identity_index, mul) for a group spec."""
    if spec[0] == 'cyc':
        m = spec[1]
        return m, 0, (lambda a, b, m=m: (a + b) % m)
    if spec[0] == 'aff':
        return _affine(spec[1])
    return _matrix_group(spec[1], spec[2])


def _perm_maker(m, mul):
    """Right-multiplication permutations g -> g*s, cached per s for one search attempt."""
    cache = {}

    def rp(s):
        r = cache.get(s)
        if r is None:
            r = [mul(g, s) for g in range(m)]
            cache[s] = r
        return r

    return rp


def _haar_cost(m, S, D, rp, e):
    """Number of (source, vertex) pairs not reached within D from A_e and B_e. Zero means valid."""
    N = 2 * m
    adj = [[] for _ in range(N)]
    for s in S:
        r = rp(s)
        for g in range(m):
            h = m + r[g]
            adj[g].append(h)
            adj[h].append(g)
    total = 0
    for src in (e, m + e):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _search_haar(m, d, D, rp, e, rng, deadline, iters):
    """Anneal a d-subset S of G so the Haar-type graph has diameter <= D. Returns S or None."""
    S = rng.sample(range(m), d)
    cur = _haar_cost(m, S, D, rp, e)
    T = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(m)
        if x in S:
            continue
        new = list(S)
        new[i] = x
        c = _haar_cost(m, new, D, rp, e)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = new, c
        T = max(0.2, T * 0.999)
    return S if cur == 0 else None


def _haar_edges(m, S, rp):
    """Edge list of the Haar-type graph: A_g = g, B_h = m + h, A_g -- B_{g*s}."""
    return [(g, m + r[g]) for s in S for r in (rp(s),) for g in range(m)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D < 4:
        return best

    # Main search: Haar-type graphs over groups, climbing the order ladder.
    # Each success doubles as a new target: the next group must have order > best_n / 2.
    groups = {}
    while time.monotonic() < deadline:
        T = max(best_n // 2 + 1, d + 1)
        specs = _group_specs(T, 2 * T + 4)
        if specs and rng.random() < 0.8:
            spec = rng.choice(specs[:4])[1]
        else:
            spec = ('cyc', rng.randint(T, 2 * T + 4))
        if spec not in groups:
            groups[spec] = _build_group(spec)
        m, e, mul = groups[spec]
        if m < d + 1:
            continue
        rp = _perm_maker(m, mul)
        S = _search_haar(m, d, D, rp, e, rng, deadline, 2500)
        if S is not None:
            consider(2 * m, _haar_edges(m, S, rp))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
