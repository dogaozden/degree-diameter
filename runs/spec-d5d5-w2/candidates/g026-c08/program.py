import math
import random
import time

import lib


MAX_GROUPS = 8        # groups tried per order N before moving on
CLIMB_ITERS = 800     # annealing steps per group in the Bi-Cayley phase
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

def _better(best, n, e, d, D):
    """Return (n, e) if it is larger than best and passes the exact validity check."""
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Phase A (all D >= 4): Bi-Cayley lifts over Z_m x|_r Z_k with annealed S.
# ----------------------------------------------------------------------------

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
    """Cached (order, mul, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count (source, target) pairs not within distance D, from A_0 and B_0."""
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over a connection set S (identity fixed as one dart)."""
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


def _bicayley_phase(d, D, rng, deadline, best, moore):
    """Search Bi-Cayley lifts with orders just above the current best."""
    tried = {}
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        window = max(2, lo // 10)
        hi = min(lo + window, moore // 2 + 1)
        N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
        tried[N] = tried.get(N, 0) + 1
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, _, T, invs = _tables(m, k2, r)
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            best = _better(best, 2 * N, edges, d, D)
    return best


# ----------------------------------------------------------------------------
# Phase B (D = 5): annealing over d-regular bipartite graphs by edge switches.
# Cost = number of unordered vertex pairs at distance > D (zero means valid).
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Unordered pairs at distance > D, via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _rewire(adj, x1, y1, x2, y2, nx1, ny1, nx2, ny2):
    """Remove edges (x1,y1), (x2,y2) and add (nx1,ny1), (nx2,ny2)."""
    adj[x1].discard(y1)
    adj[y1].discard(x1)
    adj[x2].discard(y2)
    adj[y2].discard(x2)
    adj[nx1].add(ny1)
    adj[ny1].add(nx1)
    adj[nx2].add(ny2)
    adj[ny2].add(nx2)


def _anneal_regular_one(h, d, D, rng, deadline):
    """Try to find a d-regular bipartite graph on 2h vertices with diameter <= D."""
    n = 2 * h
    adj = [set() for _ in range(n)]
    E = []
    for a in range(h):
        for s in range(d):
            b = h + (a + s) % h
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))
    cur = _bad_pairs(n, adj, D)
    if cur == 0:
        return E
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0 = max(1.0, 0.02 * cur)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = T0 * (1.0 - frac) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        _rewire(adj, a1, b1, a2, b2, a1, b2, a2, b1)
        new = _bad_pairs(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            cur = new
        else:
            _rewire(adj, a1, b2, a2, b1, a1, b1, a2, b2)
    return E if cur == 0 else None


def _regular_phase(d, D, h, rng, deadline, best):
    """Repeatedly seek valid regular bipartite graphs with h+1 per side."""
    while time.monotonic() < deadline:
        E = _anneal_regular_one(h, d, D, rng, deadline)
        if E is None:
            break
        best = _better(best, 2 * h, [(a, b) for a, b in E], d, D)
        h += 1
    return best


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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _better(best, pg[0], pg[1], d, D)
        return best

    if D == 5:
        # Phase A gets 40% of the budget, phase B gets the rest.
        best = _bicayley_phase(d, D, rng, start + 0.4 * budget, best, moore)
        h = best[0] // 2 + 1
        best = _regular_phase(d, D, h, rng, deadline, best)
    else:
        best = _bicayley_phase(d, D, rng, deadline, best, moore)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
