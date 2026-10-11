import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline for D = 3 (the calibration case d=3, D=3 gives PG(2,2)).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products Z_m x|_r Z_k.
#
# Vertices A_x = x and B_y = N + y (x, y in G). Edge A_x ~ B_{x*g} for g in S,
# so both sides are d-regular with |S| = d. Left translation is an automorphism
# that acts transitively on each side, so checking distances from A_0 and B_0
# suffices for the diameter.
#
# Search families used for D >= 4:
#   (a) greedy construction of S (add the element that minimises unreached
#       pairs, over a random sample of candidates), then 1-swap hill climbing;
#   (b) simulated annealing over S (the parent's family, kept as a hedge).
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N before moving on
CLIMB_ITERS = 800     # annealing steps per group
SWAP_ITERS = 300      # 1-swap hill-climb steps after greedy
GREEDY_SAMPLE = 40    # candidates examined per greedy step
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (T, invs): T[x][g] = x*g and invs[g] = g^-1 for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
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
    return total


def _greedy_set(N, T, invs, d, D, rng, deadline):
    """Grow S from {0} one element at a time, each time taking the best sampled candidate."""
    S = [0]
    while len(S) < d and time.monotonic() < deadline:
        cands = [c for c in range(1, N) if c not in S]
        if len(cands) > GREEDY_SAMPLE:
            cands = rng.sample(cands, GREEDY_SAMPLE)
        best_c, best_v = None, None
        for c in cands:
            v = _unreached(N, T, invs, S + [c], D)
            if best_v is None or v < best_v or (v == best_v and rng.random() < 0.5):
                best_c, best_v = c, v
        if best_c is None:
            break
        S.append(best_c)
    return S


def _swap_search(N, T, invs, S, d, D, rng, deadline):
    """1-swap plateau walk on a full-size S (identity kept at index 0)."""
    cur = list(S)
    cv = _unreached(N, T, invs, cur, D)
    for _ in range(SWAP_ITERS):
        if cv == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in cur:
            continue
        cand = cur[:]
        cand[i] = c
        v = _unreached(N, T, invs, cand, D)
        if v <= cv:
            cur, cv = cand, v
    return cur if cv == 0 else None


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S (identity fixed at index 0); returns valid S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
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

    # Bi-Cayley search: aim above the current best order N, sweeping a window
    # of orders and preferring the least-tried one.
    tried = {}
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        window = max(3, lo // 15)
        hi = min(lo + window, moore // 2 + 1)
        N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
        tried[N] = tried.get(N, 0) + 1

        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            T, invs = _tables(m, k2, r)
            if rng.random() < 0.5:
                S = _greedy_set(N, T, invs, d, D, rng, deadline)
                S = _swap_search(N, T, invs, S, d, D, rng, deadline) if len(S) == d else None
            else:
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
