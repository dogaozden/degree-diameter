import math
import random
import time

import lib


MAX_GROUPS = 12        # groups tried per order N in the bi-Cayley baseline
CLIMB_ITERS = 1000     # annealing steps per group
_BIG = 10 ** 9
_TABLE_CACHE = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: bitset ball counting on an explicit adjacency list, used as the
# objective for a switch-based repair search (see _repair below).
# ----------------------------------------------------------------------------

def _balls(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    return sum(n - r.bit_count() for r in _balls(n, adj, D)) // 2


# ----------------------------------------------------------------------------
# NEW: repair search. Start from a d-regular bipartite Haar graph on N+N
# vertices, randomize it with degree-preserving 2-switches, then anneal the
# switches to minimise the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _swap(Aadj, adj, N, a, b, c, e):
    """Replace edges (a,b) and (c,e) by (a,e) and (c,b). Requires a!=c, b!=e, e not in Aadj[a], b not in Aadj[c]."""
    Aadj[a].discard(b)
    Aadj[a].add(e)
    Aadj[c].discard(e)
    Aadj[c].add(b)
    adj[a].remove(N + b)
    adj[a].append(N + e)
    adj[c].remove(N + e)
    adj[c].append(N + b)
    adj[N + b].remove(a)
    adj[N + b].append(c)
    adj[N + e].remove(c)
    adj[N + e].append(a)


def _repair(N, d, D, rng, deadline):
    """Try to find a d-regular bipartite graph on N+N vertices with diameter <= D.

    Returns (2N, edges) on success, else None.
    """
    shifts = rng.sample(range(N), d)
    Aadj = [set((i + s) % N for s in shifts) for i in range(N)]
    adj = [[] for _ in range(2 * N)]
    E = []
    for i in range(N):
        for j in Aadj[i]:
            adj[i].append(N + j)
            adj[N + j].append(i)
            E.append([i, j])
    m = len(E)

    # Free randomisation: accept every valid switch without evaluating it.
    for _ in range(4 * m):
        i, j = rng.randrange(m), rng.randrange(m)
        a, b = E[i]
        c, e = E[j]
        if i == j or a == c or b == e or e in Aadj[a] or b in Aadj[c]:
            continue
        _swap(Aadj, adj, N, a, b, c, e)
        E[i] = [a, e]
        E[j] = [c, b]

    cost = _bad_pairs(2 * N, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now > deadline:
                break
            frac = (now - t0) / span
            T = 0.1 + 1.0 * (1.0 - frac)
        i, j = rng.randrange(m), rng.randrange(m)
        a, b = E[i]
        c, e = E[j]
        if i == j or a == c or b == e or e in Aadj[a] or b in Aadj[c]:
            continue
        _swap(Aadj, adj, N, a, b, c, e)
        new = _bad_pairs(2 * N, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            E[i] = [a, e]
            E[j] = [c, b]
        else:
            _swap(Aadj, adj, N, a, e, c, b)

    if cost == 0:
        return 2 * N, [(i, N + j) for i in range(N) for j in Aadj[i]]
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (baseline for the first part of the budget).
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N."""
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
    """Pairs (source, target) not within distance D, from A_0 and B_0."""
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
    """Simulated annealing over a connection set S containing the identity."""
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

    best = lib.haar_graph(d, range(d))   # K_{d,d}, always valid for D >= 2
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))

    # Phase 1 (about 30% of budget): bi-Cayley lifts to get a solid baseline.
    bc_deadline = start + 0.3 * budget
    try:
        while best[0] < moore and time.monotonic() < bc_deadline:
            lo = best[0] // 2 + 1
            if lo > moore // 2:
                break
            N = lo + rng.randrange(max(2, lo // 10))
            if N < d:
                continue
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > bc_deadline:
                    break
                _, _, T, invs = _tables(m, k2, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, bc_deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
    except Exception:
        pass

    # Phase 2: repair search for orders above the current best.
    try:
        N = max(d, best[0] // 2 + 1)
        while time.monotonic() < deadline and N <= moore // 2:
            now = time.monotonic()
            slice_end = min(deadline, now + max(4.0, (deadline - now) * 0.5))
            res = _repair(N, d, D, rng, slice_end)
            if res is not None:
                consider(res[0], res[1])
                N = max(N + 1, best[0] // 2 + 1)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
