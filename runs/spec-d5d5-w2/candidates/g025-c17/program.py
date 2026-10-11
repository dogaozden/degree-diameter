import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change for D >= 4: bi-Cayley graphs over a wider family of groups.
#
# Instead of the Z_m x| Z_k lifts with multi-base annealing used before, this
# version searches only bi-Cayley graphs Gamma(G, S): vertices A_x, B_y for
# x, y in G, with A_x ~ B_{x s} for s in S. Each group is taken from two
# families: metacyclic semidirect products (lib.semidirect_group) and the
# affine groups AGL(1, p) of order p(p-1). Connection sets are searched by
# simulated annealing on the number of vertex pairs farther than D apart.
# Left translation is an automorphism, so eccentricities from A_e and B_e
# determine the diameter.
#
# Safety: every candidate is checked with lib.is_valid before it is kept, and
# K_{d,d} is the fallback. The D <= 3 cases use projective planes.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N before moving on
ANNEAL_ITERS = 1500   # annealing steps per group
_CACHE = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _table(order, mul):
    """Full multiplication table T[x][y] = x*y for elements 0..order-1 (identity is 0)."""
    return [[mul(x, y) for y in range(order)] for x in range(order)]


def _inverse_list(order, T):
    """inv[x] is the index of x^-1, found from the multiplication table."""
    inv = [0] * order
    for x in range(order):
        row = T[x]
        for y in range(order):
            if row[y] == 0:
                inv[x] = y
                break
    return inv


def _agl_table(p):
    """Affine group AGL(1, p) of order p(p-1); element (a, b) with x -> a*x + b coded as (a-1)*p + b."""
    G = p * (p - 1)

    def mul(x, y):
        a1, b1 = x // p + 1, x % p
        a2, b2 = y // p + 1, y % p
        a = a1 * a2 % p
        b = (a1 * b2 + b1) % p
        return (a - 1) * p + b

    return _table(G, mul)


def _sd_params(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("sd", m, k, r))
    return out


def _candidate_groups(N):
    """Keys for groups of order N from the metacyclic and affine families."""
    out = _sd_params(N)
    for p in range(2, N + 2):
        if p * (p - 1) == N and _is_prime(p):
            out.append(("agl", p))
    return out


def _group(key):
    """Cached (order, T, inverses) for a group key."""
    hit = _CACHE.get(key)
    if hit is not None:
        return hit
    if key[0] == "sd":
        _, m, k, r = key
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = _table(order, mul)
    else:
        _, p = key
        order = p * (p - 1)
        T = _agl_table(p)
    hit = (order, T, _inverse_list(order, T))
    if len(_CACHE) >= 12:
        _CACHE.clear()
    _CACHE[key] = hit
    return hit


def _unreached(G, T, invs, S, D):
    """Count pairs at distance > D from A_e (index 0) and B_e (index G), over both sides.

    A_x ~ B_{x s} for s in S. From B_y the neighbours are A_{y s^-1}.
    """
    Sinv = [invs[s] for s in S]
    total = 0
    for src in (0, G):
        seen = bytearray(2 * G)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = T[u]
                    for s in S:
                        v = G + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - G]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * G - count
    return total


def _anneal(G, T, invs, d, D, rng, iters, deadline):
    """Anneal over connection sets S with identity fixed in S (WLOG). Returns S if it has diameter <= D."""
    if G < d:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    cur = _unreached(G, T, invs, S, D)
    best_v, best_S = cur, S[:]
    T0 = 2.0 + 0.02 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.05
        i = rng.randrange(1, d)
        c = rng.randrange(1, G)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(G, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            if cur < best_v:
                best_v, best_S = cur, S[:]
        else:
            S[i] = old
    return best_S if best_v == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    # D >= 4: bi-Cayley search. Each found graph has 2G vertices.
    try:
        tried = {}
        hi_cap = moore // 2
        while time.monotonic() < deadline:
            lo = best[0] // 2 + 1
            if lo > hi_cap:
                break
            hi = min(hi_cap, lo + max(6, lo // 8)) + 1
            N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1
            if N < d:
                continue
            cands = _candidate_groups(N)
            rng.shuffle(cands)
            found = None
            for key in cands[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                G, T, invs = _group(key)
                S = _anneal(G, T, invs, d, D, rng, ANNEAL_ITERS, deadline)
                if S is not None:
                    found = (G, T, S)
                    break
            if found is not None:
                G, T, S = found
                edges = [(x, G + T[x][s]) for x in range(G) for s in S]
                consider(2 * G, edges)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
