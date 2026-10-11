import math
import random
import time

import lib

# Bold change: instead of only the metacyclic bi-Cayley family, search bi-Cayley
# graphs over affine groups F_q x| H (H a subgroup of F_q^*, order >= 3) and
# non-metacyclic semidirect products, for orders N in [lo, moore/2]. Each group
# gets short hill-climb slices in round-robin order. Every candidate passes
# lib.is_valid before it is kept, and K_{d,d} (or the PG(2,q) incidence graph for
# D = 3) is the fallback, so a valid graph is always returned.

_BIG = 10 ** 9
SLICE = 3.0      # seconds per group per pass
STALL_LIMIT = 400


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _aff_table(q, h):
    """Multiplication table of F_q x| H, H the order-h subgroup of F_q^*.

    Element (a, j) is coded as a*h + j and multiplies as (a, j)(c, l) = (a + w^j c, j + l),
    where w generates H. Identity is code 0.
    """
    F = lib.GF(q)
    addT = F.add_table.tolist()
    mulT = F.mul_table.tolist()
    w = F.pow(F.primitive_element(), (q - 1) // h)
    wp = [1] * h
    for j in range(1, h):
        wp[j] = mulT[wp[j - 1]][w]
    N = q * h
    T = []
    for x in range(N):
        a, j = divmod(x, h)
        row = [0] * N
        for y in range(N):
            c, l = divmod(y, h)
            row[y] = addT[a][mulT[wp[j]][c]] * h + (j + l) % h
        T.append(row)
    return N, T


def _sd_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k from the library."""
    N, mul, _ = lib.semidirect_group(m, k, r)
    return N, [[mul(x, y) for y in range(N)] for x in range(N)]


def _group(spec):
    """Build the (N, T) table for a pool spec; None if the group is invalid."""
    try:
        if spec[0] == "aff":
            return _aff_table(spec[1], spec[2])
        return _sd_table(spec[1], spec[2], spec[3])
    except Exception:
        return None


def _pool(lo, hi, rng):
    """Interleaved list of affine groups (ascending order) and semidirect groups with N in [lo, hi]."""
    affs = []
    for q in range(2, hi + 1):
        if not lib.is_prime_power(q):
            continue
        for h in range(3, q):
            if (q - 1) % h == 0 and lo <= q * h <= hi:
                affs.append(("aff", q, h, q * h))
    affs.sort(key=lambda s: s[-1])

    sds = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    sds.append(("sd", m, k, r, N))
    rng.shuffle(sds)
    sds = sds[:40]

    pool = []
    for i in range(max(len(affs), len(sds))):
        if i < len(affs):
            pool.append(affs[i])
        if i < len(sds):
            pool.append(sds[i])
    return pool


def _unreached(N, T, invs, S, D, cap):
    """Pairs (source, target) not within distance D, for sources A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translations are automorphisms,
    so eccentricities from A_0 and B_0 determine the whole graph. Returns early once
    the total exceeds cap.
    """
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
        if total > cap:
            return total
    return total


def _climb(N, T, invs, d, D, rng, deadline):
    """Hill-climb a d-element connection set S containing the identity (WLOG) to zero unreached pairs."""
    if N - 1 < d - 1:
        return None

    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D, _BIG)

    S, cur = fresh()
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D, cur)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            pg = _pg_fallback(d)
            if pg is not None:
                consider(pg[0], pg[1])
    except Exception:
        pass

    moore = lib.moore_bound(d, D)
    hi = moore // 2  # bi-Cayley lifts have 2N vertices

    try:
        lo = max(best[0] // 2 + 1, hi // 2)
        if lo <= hi:
            pool = _pool(lo, hi, rng)
            while pool and time.monotonic() < deadline:
                attempted = False
                for spec in pool:
                    now = time.monotonic()
                    if now >= deadline:
                        break
                    if 2 * spec[-1] <= best[0]:
                        continue
                    grp = _group(spec)
                    if grp is None:
                        continue
                    N, T = grp
                    invs = [row.index(0) for row in T]
                    attempted = True
                    S = _climb(N, T, invs, d, D, rng, min(deadline, now + SLICE))
                    if S is not None:
                        edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                        consider(2 * N, edges)
                if not attempted:
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
