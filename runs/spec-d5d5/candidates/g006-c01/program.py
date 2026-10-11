import math
import random
import time

import lib

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
N_WINDOW = 8
SEED_SHARE = 0.45
REPAIR_T = 1.5


# ----------------------------------------------------------------------------
# Stage 1: bi-Cayley seed lifts over semidirect products Z_m x| Z_k.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N giving Z_m x|_r Z_k."""
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
    """Multiplication table T[x][g] = x*g and inverse table for Z_m x|_r Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return T, invs


def _unreached(N, T, invs, S, D):
    """Pairs not within D, counted from A_0 and B_0 (enough by vertex-transitivity per side)."""
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
    """Hill-climb a connection set S (containing identity) to zero unreached pairs."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        stall = 0 if v < cur else stall + 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _bicayley_lift(d, D, N, rng, deadline):
    """Try several groups of order N; return (2N, edges, As, Bs) for a valid lift, else None."""
    if d < 2 or N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T, invs = _tables(m, k, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            return 2 * N, edges, list(range(N)), list(range(N, 2 * N))
    return None


# ----------------------------------------------------------------------------
# Stage 2: simulated-annealing vertex insertion.
# Each step adds one A vertex and one B vertex, then repairs the graph with
# degree-preserving edge swaps and deficit-filling edge additions until every
# pair is within distance D again.
# ----------------------------------------------------------------------------

def _cost(n, adj, d, D):
    """(bad unordered pairs at distance > D, total degree deficit)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    bad = sum(n - r.bit_count() for r in reach) // 2
    deficit = sum(d - len(a) for a in adj)
    return bad, deficit


def _toggle(adj, x, y, on):
    if on:
        adj[x].add(y)
        adj[y].add(x)
    else:
        adj[x].discard(y)
        adj[y].discard(x)


def _repair(n, As, Bs, adj, d, D, rng, deadline):
    """Anneal until bad == 0. Returns True on success; the graph stays degree-bounded throughout."""
    bad, deficit = _cost(n, adj, d, D)
    cur = 4 * bad + deficit
    while bad > 0:
        if time.monotonic() > deadline:
            return False
        defA = [a for a in As if len(adj[a]) < d]
        defB = [b for b in Bs if len(adj[b]) < d]
        if defA and defB and rng.random() < 0.4:
            a = rng.choice(defA)
            b = rng.choice(defB)
            if b in adj[a]:
                continue
            revert = [(a, b, False)]
            _toggle(adj, a, b, True)
        else:
            a1 = rng.choice(As)
            a2 = rng.choice(As)
            if a1 == a2 or not adj[a1] or not adj[a2]:
                continue
            b1 = rng.choice(list(adj[a1]))
            b2 = rng.choice(list(adj[a2]))
            if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            revert = [(a1, b2, False), (a2, b1, False), (a1, b1, True), (a2, b2, True)]
            _toggle(adj, a1, b1, False)
            _toggle(adj, a2, b2, False)
            _toggle(adj, a1, b2, True)
            _toggle(adj, a2, b1, True)
        bad2, def2 = _cost(n, adj, d, D)
        c2 = 4 * bad2 + def2
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / REPAIR_T):
            cur, bad, deficit = c2, bad2, def2
        else:
            for x, y, on in revert:
                _toggle(adj, x, y, on)
    return True


def _grow(n, edges, As, Bs, d, D, deadline, rng):
    """Repeatedly insert a vertex pair and repair; return the largest valid (n, edges) reached."""
    moore = lib._moore_bound(d, D)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    As = list(As)
    Bs = list(Bs)
    best = (n, list(edges))
    while time.monotonic() < deadline and n + 2 <= moore:
        As.append(n)
        Bs.append(n + 1)
        adj.append(set())
        adj.append(set())
        n += 2
        if not _repair(n, As, Bs, adj, d, D, rng, deadline):
            break
        best = (n, [(a, b) for a in As for b in adj[a]])
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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Seed: PG(2, q) incidence for D = 3, otherwise a bi-Cayley lift.
    seed_graph = None
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n2, e2 = lib.projective_plane_incidence(q)
                m = n2 // 2
                seed_graph = (n2, e2, list(range(m)), list(range(m, n2)))
                consider(n2, e2)
                break

    if D >= 4 or seed_graph is None:
        seed_deadline = start + SEED_SHARE * budget
        cur_half = max(d, 2)
        while time.monotonic() < seed_deadline and 2 * cur_half <= moore:
            N = cur_half + rng.randrange(N_WINDOW)
            res = _bicayley_lift(d, D, N, rng, seed_deadline)
            if res is not None:
                nl, el, As0, Bs0 = res
                consider(nl, el)
                if seed_graph is None or nl > seed_graph[0]:
                    seed_graph = res
                cur_half = N + 1

    if seed_graph is None:
        seed_graph = (best[0], best[1], list(range(d)), list(range(d, 2 * d)))

    # Grow the seed by annealed vertex insertion over the remaining time.
    n_s, e_s, As0, Bs0 = seed_graph
    if n_s + 2 <= moore and time.monotonic() < deadline:
        n_g, e_g = _grow(n_s, e_s, As0, Bs0, d, D, deadline, rng)
        consider(n_g, e_g)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
