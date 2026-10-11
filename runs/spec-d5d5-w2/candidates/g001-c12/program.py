import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family A: edge-switch annealing on bipartite d-regular graphs.
# Start from a Haar-type circulant bipartite graph, then apply degree-preserving
# edge switches (a1-b1, a2-b2 -> a1-b2, a2-b1) and minimise the number of vertex
# pairs at distance > D. Stop when the cost reaches zero.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset balls)."""
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


def _switch_anneal(d, D, N, rng, t_end):
    """Anneal a d-regular bipartite graph on N+N vertices; return edges or None."""
    shifts = rng.sample(range(N), d)
    E = [[i, N + (i + s) % N] for i in range(N) for s in shifts]
    n = 2 * N
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    cost = _bad(n, adj, D)
    if cost == 0:
        return [(a, b) for a, b in E]

    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    T0 = max(1.0, 0.03 * cost)
    T1 = 0.2
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            return None
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if b2 in adj[a1] or b1 in adj[a2]:
            continue
        # apply switch
        adj[a1].discard(b1); adj[b1].discard(a1)
        adj[a2].discard(b2); adj[b2].discard(a2)
        adj[a1].add(b2); adj[b2].add(a1)
        adj[a2].add(b1); adj[b1].add(a2)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            # revert
            adj[a1].discard(b2); adj[b2].discard(a1)
            adj[a2].discard(b1); adj[b1].discard(a2)
            adj[a1].add(b1); adj[b1].add(a1)
            adj[a2].add(b2); adj[b2].add(a2)
    return [(a, b) for a, b in E]


# ----------------------------------------------------------------------------
# Family B: Bi-Cayley lifts over semidirect products Z_m x| Z_k with an
# annealed connection set (one base vertex per side).
# ----------------------------------------------------------------------------

CLIMB_ITERS = 800
MAX_GROUPS = 6


def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, T, invs, S, D):
    """Pairs not within D, checked from A_0 and B_0 (vertex-transitive on each side)."""
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


def _bicayley_attempt(d, D, N, rng, deadline):
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        invs = [inv(g) for g in range(order)]
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return [(x, N + T[x][g]) for x in range(N) for g in S]
    return None


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
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n, e = lib.haar_graph(D, [0, 1])  # cycle C_{2D}
        if lib.is_valid(n, e, d, D):
            return n, e
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best[0], best[1]

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines for D = 3.
    if D == 3:
        try:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    consider(*lib.projective_plane_incidence(q))
                    break
        except Exception:
            pass
        try:
            q = d - 2
            if q >= 3 and lib.is_prime_power(q):
                consider(*lib.araujo_lopez_graph(q))
        except Exception:
            pass

    # Phase 1: Bi-Cayley lifts (about 35% of the budget).
    t1 = start + 0.35 * budget
    try:
        while time.monotonic() < t1 and best[0] < moore:
            lo = best[0] // 2 + 1
            if lo > moore // 2:
                break
            hi = min(lo + max(2, lo // 10), moore // 2 + 1)
            N = rng.randrange(lo, hi)
            edges = _bicayley_attempt(d, D, N, rng, t1)
            if edges is not None:
                consider(2 * N, edges)
    except Exception:
        pass

    # Phase 2: switch annealing, growing the order one side at a time.
    try:
        N = max(d, best[0] // 2 + 1)
        while time.monotonic() < deadline and best[0] < moore:
            if 2 * N > moore:
                break
            now = time.monotonic()
            slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
            res = _switch_anneal(d, D, N, rng, slice_end)
            if res is not None:
                consider(2 * N, res)
                N = max(N + 1, best[0] // 2 + 1)
            # on failure, retry the same N from a fresh random start
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], best[1]
