"""Bold variant for D >= 3: a bi-Cayley start followed by augmentation with
bitset-based repair annealing.

Stage A: search bi-Cayley graphs over semidirect products Z_m x| Z_k, one base
vertex per side (A_x ~ B_{xg} for g in S), keeping the largest order found.

Stage B: starting from that graph (or K_{d,d}), repeatedly add one vertex per
side. Each new vertex takes d edges by switching them out of existing edges,
then degree-preserving edge swaps anneal the number of vertex pairs at
distance > D down to zero. Every returned graph passes lib.is_valid, and the
fallback is K_{d,d}.
"""
import math
import random
import time

import lib

ITERS_A = 350       # annealing steps per (N, group) in stage A
MAX_GROUPS = 6      # groups tried per order N in stage A
ANNEAL_B = 1200     # repair-annealing steps per augmentation in stage B
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Stage A: bi-Cayley search over semidirect products.
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
    """Cached (T, invs): T[x][g] = x*g and invs[g] = g^{-1} for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TABLE_CACHE) >= 32:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Vertex pairs not within distance D, counted from sources A_0 and B_0."""
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


def _anneal_S(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_search(d, D, rng, deadline, lo, hi):
    """Sweep orders N = lo..hi; return (N, edges) for the largest N found."""
    best = None
    for N in range(lo, hi + 1):
        if time.monotonic() > deadline:
            break
        if N <= d:
            continue
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            T, invs = _tables(m, k, r)
            S = _anneal_S(N, T, invs, d, D, rng, ITERS_A, deadline)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            best = (N, edges)
    return best


# ----------------------------------------------------------------------------
# Stage B: augmentation plus repair annealing on explicit bipartite graphs.
# Vertices 0..n/2-1 form side A, n/2..n-1 form side B.
# ----------------------------------------------------------------------------

def _state_from(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    half = n // 2
    side = [0 if v < half else 1 for v in range(n)]
    return adj, side


def _edges_of(n, adj, side):
    return [(x, y) for x in range(n) if side[x] == 0 for y in adj[x]]


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset balls)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _augment(n, adj, side, d, rng):
    """Add one A vertex a and one B vertex b, each of degree d, by switching d disjoint edges.

    Returns the new vertex count n + 2, or None if too few disjoint edges exist.
    """
    edges = _edges_of(n, adj, side)
    rng.shuffle(edges)
    used_x, used_y, chosen = set(), set(), []
    for x, y in edges:
        if x in used_x or y in used_y:
            continue
        chosen.append((x, y))
        used_x.add(x)
        used_y.add(y)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    a = n
    b = n + 1
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    for x, y in chosen:
        adj[x].discard(y)
        adj[y].discard(x)
        adj[a].add(y)
        adj[y].add(a)
        adj[x].add(b)
        adj[b].add(x)
    return n + 2


def _anneal_graph(n, adj, side, D, rng, deadline, iters):
    """Degree-preserving bipartite edge swaps that drive _bad to zero. Returns True on success."""
    E = _edges_of(n, adj, side)
    cur = _bad(n, adj, D)
    it = 0
    while cur > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        T = 0.6 * (1.0 - it / iters) + 0.05
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        x, y = E[i]
        x2, y2 = E[j]
        if x == x2 or y == y2 or y2 in adj[x] or y in adj[x2]:
            continue
        adj[x].discard(y)
        adj[y].discard(x)
        adj[x2].discard(y2)
        adj[y2].discard(x2)
        adj[x].add(y2)
        adj[y2].add(x)
        adj[x2].add(y)
        adj[y].add(x2)
        new = _bad(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            E[i] = (x, y2)
            E[j] = (x2, y)
        else:
            adj[x].discard(y2)
            adj[y2].discard(x)
            adj[x2].discard(y)
            adj[y].discard(x2)
            adj[x].add(y)
            adj[y].add(x)
            adj[x2].add(y2)
            adj[y2].add(x2)
    return cur == 0


def _stage_b(n, adj, side, d, D, rng, deadline, best):
    """Repeatedly augment and repair until the deadline; returns the best valid (n, edges)."""
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_side = list(side)
        n2 = _augment(n, adj, side, d, rng)
        if n2 is None:
            break
        ok = _anneal_graph(n2, adj, side, D, rng, deadline, ANNEAL_B)
        if ok:
            n = n2
            e2 = _edges_of(n, adj, side)
            if n > best[0] and lib.is_valid(n, e2, d, D):
                best = (n, e2)
        else:
            adj, side = snap_adj, snap_side
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: bipartite, degree d, diameter 2. Safe fallback for every D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if D == 2:
        return fb_n, fb_e
    best = (fb_n, fb_e)

    moore = lib.moore_bound(d, D)

    # D = 3 with d-1 a prime power: projective plane incidence graph meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Stage A: bi-Cayley start (first 35% of the budget).
    stage_a_deadline = start + 0.35 * budget
    lo = max(d + 1, 40)
    hi = max(lo, moore // 2)
    base = _bicayley_search(d, D, random.Random(seed * 1000003 + 17),
                            stage_a_deadline, lo, hi)

    if base is not None:
        N, e = base
        if 2 * N > best[0] and lib.is_valid(2 * N, e, d, D):
            best = (2 * N, e)
        start_n, start_e = best
    else:
        start_n, start_e = fb_n, fb_e

    # Stage B: augmentation with repair annealing (remaining budget).
    adj, side = _state_from(start_n, start_e)
    best = _stage_b(start_n, adj, side, d, D, rng, deadline, best)

    n, e = best
    if not lib.is_valid(n, e, d, D):
        n, e = fb_n, fb_e
    return n, e
