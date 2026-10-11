import math
import random
import time

import lib


def _ok(n, edges, d, D):
    """Full validity check; any exception counts as invalid."""
    try:
        return lib.is_valid(n, edges, d, D)
    except Exception:
        return False


def _trivial(d, D):
    """Always-valid fallback graphs."""
    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def _haar_search(d, D, rng, deadline):
    """Cyclic Haar graphs (bi-Cayley over Z_m), increasing m until repeated misses."""
    best = None
    m = d + 1
    misses = 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def _group_candidates(N, rng, cap):
    """Semidirect products Z_m x| Z_k (m*k = N), including the cyclic group, shuffled and capped."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:cap]


def _table(m, k, r):
    """Multiplication table T and inverse list I for the group (m, k, r)."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return order, T, I


def _unreached(N, T, I, S, D):
    """Bi-Cayley graph on A = {0..N-1}, B = {N..2N-1}, a_g ~ b_{g s} for s in S.

    Vertex-transitivity under left multiplication means diameter <= D iff every
    vertex is within D of a_e and of b_e. Returns the total number of unreached
    vertices from those two sources (0 means valid).
    """
    total = 0
    full = 2 * N
    for src in (0, N):
        seen = {src}
        frontier = [src]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = T[v]
                    for s in S:
                        w = N + row[s]
                        if w not in seen:
                            seen.add(w)
                            nxt.append(w)
                else:
                    row = T[v - N]
                    for s in S:
                        w = row[I[s]]
                        if w not in seen:
                            seen.add(w)
                            nxt.append(w)
            if not nxt:
                break
            frontier = nxt
        total += full - len(seen)
    return total


def _climb(N, T, I, d, D, S, deadline, rng):
    """Hill-climb on the connection set S (plateau moves allowed). Returns a valid S or None."""
    cost = _unreached(N, T, I, S, D)
    stall = 0
    while cost > 0:
        if time.monotonic() >= deadline or stall > 500:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            stall += 1
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _unreached(N, T, I, S2, D)
        if c2 < cost:
            S, cost = S2, c2
            stall = 0
        elif c2 == cost:
            S = S2
            stall += 1
        else:
            stall += 1
    return S


def _search_order(N, d, D, rng, deadline):
    """Try several groups of order N with random restarts until the deadline."""
    groups = _group_candidates(N, rng, 6)
    if not groups:
        return None
    tables = {}
    attempt = 0
    while time.monotonic() < deadline:
        key = groups[attempt % len(groups)]
        attempt += 1
        if key not in tables:
            tables[key] = _table(*key)
        order, T, I = tables[key]
        if order != N:
            continue
        S0 = rng.sample(range(N), d)
        S = _climb(N, T, I, d, D, S0, deadline, rng)
        if S is not None:
            return S, T
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.2, min(0.75 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)
    q = d - 1

    # Exact optimal construction when available.
    if D == 3 and lib.is_prime_power(q):
        res = lib.projective_plane_incidence(q)
        if _ok(res[0], res[1], d, D):
            return res

    best = (1, [])
    t = _trivial(d, D)
    if _ok(t[0], t[1], d, D):
        best = t

    # Araujo-Pardo / Lopez record construction for D = 3, d - 2 a prime power.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            res = lib.araujo_lopez_graph(d - 2)
            if _ok(res[0], res[1], d, D) and res[0] > best[0]:
                best = res
        except Exception:
            pass

    # Quick cyclic baseline.
    haar_deadline = min(deadline, time.monotonic() + 0.10 * budget)
    h = _haar_search(d, D, rng, haar_deadline)
    if h is not None and h[0] > best[0] and _ok(h[0], h[1], d, D):
        best = h

    # Bi-Cayley search over groups of growing order, starting just above the current best.
    hi = lib.moore_bound(d, D) // 2
    N = best[0] // 2 + 1
    while N <= hi and time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + 2.0)
        res = _search_order(N, d, D, rng, slice_end)
        if res is not None:
            S, T = res
            n = 2 * N
            edges = [(g, N + T[g][s]) for g in range(N) for s in S]
            if n > best[0] and _ok(n, edges, d, D):
                best = (n, edges)
        N += 1

    return best
