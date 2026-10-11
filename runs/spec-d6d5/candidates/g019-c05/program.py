import math
import random
import time

import lib


def _moore(d, D):
    """Bipartite Moore bound for max degree d and diameter D."""
    if D <= 0 or d <= 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}.
# Each of d "layers" is a perfect matching A_i -> B_{p[i]} with a voltage s_i.
# Vertex A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Edge A_{i,g} -- B_{j, g*s}.
#
# Left multiplication by any group element is an automorphism of the lift that
# acts regularly on each side. So the diameter is <= D iff every base vertex
# (identity element of its side) reaches all N vertices within D steps.
# ----------------------------------------------------------------------------

class _Perms:
    """Lazily cached right-multiplication permutations g -> g*s."""

    def __init__(self, G, mul):
        self.G = G
        self.mul = mul
        self.cache = {}

    def __getitem__(self, s):
        p = self.cache.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.G)]
            self.cache[s] = p
        return p


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    if G < 2:
        return None
    divs = [k2 for k2 in range(1, G + 1) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    for _ in range(60):
        k2 = 1 if rng.random() < 0.3 else rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(1, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _adjacency(k, G, state, perms):
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in state:
        p = perms[s]
        ai = i * G
        bj = (k + j) * G
        for g in range(G):
            a = ai + g
            b = bj + p[g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, G, D, state, perms, limit):
    """Number of (base representative, vertex) pairs at distance > D.

    Returns early with a value above `limit` once the running total exceeds it.
    Zero means the lift has diameter <= D.
    """
    N = 2 * k * G
    adj = _adjacency(k, G, state, perms)
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in srcs:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _init_state(d, k, G, rng):
    state = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            state.append([i, p[i], rng.randrange(G)])
    return state


def _anneal(d, D, k, G, perms, rng, deadline, iters, T0=1.0):
    """Simulated annealing over voltages and layer matchings. Returns (state, cost)."""
    state = _init_state(d, k, G, rng)
    cost = _cost(k, G, D, state, perms, float("inf"))
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.996)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.65 or k < 2:
            idx = rng.randrange(len(state))
            old = state[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            state[idx][2] = new
            c2 = _cost(k, G, D, state, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                state[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            state[ia][1], state[ib][1] = state[ib][1], state[ia][1]
            c2 = _cost(k, G, D, state, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                state[ia][1], state[ib][1] = state[ib][1], state[ia][1]
    return state, cost


def _edges(k, G, state, perms):
    E = set()
    for i, j, s in state:
        p = perms[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + p[g]))
    return 2 * k * G, sorted(E)


def _saturate(n, edges, d):
    """Add A-B edges between deficient vertices. Only adds edges, so diameter cannot grow."""
    half = n // 2
    deg = [0] * n
    ex = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        ex.add((min(u, v), max(u, v)))
    left = [v for v in range(half) if deg[v] < d]
    right = [v for v in range(half, n) if deg[v] < d]
    E = list(edges)
    for a in left:
        for b in right:
            if deg[a] >= d:
                break
            if deg[b] < d and (a, b) not in ex:
                ex.add((a, b))
                E.append((a, b))
                deg[a] += 1
                deg[b] += 1
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    bound = _moore(d, D)
    if best_n >= bound:
        return best

    # Main search: annealed bi-Cayley lifts over semidirect products, aiming
    # just above the current best order each time.
    KS = [1, 2, 2, 3, 3, 4, 4, 5, 6]
    slice_len = max(2.0, 0.08 * time_limit)
    while time.monotonic() < deadline and best_n < bound:
        k = rng.choice(KS)
        base = best_n // (2 * k)
        G = base + 1 + rng.randrange(0, max(2, base // 25))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        perms = _Perms(order, mul)
        slice_end = min(deadline, time.monotonic() + slice_len)
        state, c = _anneal(d, D, k, order, perms, rng, slice_end, 4000)
        if c == 0:
            n, e = _edges(k, order, state, perms)
            e = _saturate(n, e, d)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
