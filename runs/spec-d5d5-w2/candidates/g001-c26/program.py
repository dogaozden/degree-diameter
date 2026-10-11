import math
import random
import time

import lib

# Cache of group multiplication tables, kept small because each table is O(N^2).
_TABLES = {}
_MAX_N = 1200          # largest group order handled with explicit tables
_MAX_CACHE = 4


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


def _group_table(m, k, r):
    """Cached (order, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLES) >= _MAX_CACHE:
        _TABLES.clear()
    _TABLES[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of vertex pairs not within distance D, counted from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x s} for s in S. Left translation is an
    automorphism that is transitive on each side, so two sources suffice.
    """
    Sinv = [invs[s] for s in S]
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
                    for s in S:
                        v = N + row[s]
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


def _ils(N, T, invs, d, D, rng, deadline, samples):
    """Iterated local search over connection sets S (identity fixed in S[0]).

    Each move picks a position and replaces it with the best of a random
    sample of candidates (plateau moves accepted with some probability).
    When a full pass stalls, two random positions are perturbed.
    Returns a valid S (zero unreached pairs) or None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = list(S), cur
    while best_v and time.monotonic() < deadline:
        improved = False
        pos = list(range(1, d))
        rng.shuffle(pos)
        for i in pos:
            if time.monotonic() >= deadline:
                break
            used = set(S)
            pick, pick_v = None, None
            for c in rng.sample(range(1, N), min(samples, N - 1)):
                if c in used:
                    continue
                S2 = S[:]
                S2[i] = c
                v = _unreached(N, T, invs, S2, D)
                if pick_v is None or v < pick_v or (v == pick_v and rng.random() < 0.5):
                    pick, pick_v = c, v
                    if v == 0:
                        break
            if pick is None:
                continue
            if pick_v < cur or (pick_v == cur and rng.random() < 0.3):
                if pick_v < cur:
                    improved = True
                S[i] = pick
                cur = pick_v
                if cur < best_v:
                    best_v = cur
                    best_S = list(S)
                    if best_v == 0:
                        break
        if best_v == 0:
            break
        if not improved:
            for i in rng.sample(range(1, d), min(2, d - 1)):
                c = rng.randrange(1, N)
                while c in S:
                    c = rng.randrange(1, N)
                S[i] = c
            cur = _unreached(N, T, invs, S, D)
    return best_S if best_v == 0 else None


def _is_pg_case(d, D):
    return D == 3 and lib.is_prime_power(d - 1)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed * 1000003 + d * 101 + D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured construction for D = 3 when d - 1 is a prime power.
    if _is_pg_case(d, D):
        consider(*lib.projective_plane_incidence(d - 1))
    if best[0] >= moore:
        return best

    # Main family: bi-Cayley lifts over semidirect products Z_m x|_r Z_k,
    # searched by iterated best-of-sample coordinate moves. Orders are swept
    # in a window just above the current best.
    GROUPS_PER_N = 4
    hi_cap = min(moore // 2, _MAX_N)
    tried = {}
    while best[0] < moore and time.monotonic() < deadline:
        lo = max(best[0] // 2 + 1, 2 * d)
        if lo > hi_cap:
            break
        window = max(3, lo // 25)
        hi = min(lo + window, hi_cap + 1)
        N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
        tried[N] = tried.get(N, 0) + 1

        slice_end = min(deadline, time.monotonic() + max(2.0, budget * 0.1))
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k2, r in groups[:GROUPS_PER_N]:
            if time.monotonic() >= slice_end:
                break
            _, T, invs = _group_table(m, k2, r)
            S = _ils(N, T, invs, d, D, rng, slice_end, 30)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + T[x][s]) for x in range(N) for s in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
