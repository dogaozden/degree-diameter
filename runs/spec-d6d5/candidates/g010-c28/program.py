import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: non-cyclic bi-Cayley lifts with k base vertices per side.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h, for i, j in 0..k-1.
# Layer L has a permutation p_L of 0..k-1 and voltages s_{L,i}. Dart (L, i)
# joins A_i,g to B_{p_L[i]}, mul(g, s_{L,i}) for all g. Each vertex then gets
# exactly one edge per layer, so the graph is d-regular and bipartite.
#
# The search anneals the permutations and voltages with a cost equal to the
# number of ordered vertex pairs at distance > D. Cost 0 means the lift is valid.
# Each successful lift becomes the new target, so the order increases over time.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    divs = [t for t in range(2, G + 1) if G % t == 0 and G // t >= 2]
    if divs and rng.random() < 0.85:
        k2 = rng.choice(divs)
    else:
        k2 = 1
    m = G // k2
    if m < 2:
        return None
    if k2 == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    try:
        order, mul, _ = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    return order, mul


def _lift_edges(k, G, R, P, S):
    """Edge set of the bi-Cayley lift described by permutations P and voltages S."""
    E = set()
    for L in range(len(P)):
        p = P[L]
        s = S[L]
        for i in range(k):
            Rs = R[s[i]]
            ba = i * G
            bb = (k + p[i]) * G
            for g in range(G):
                E.add((ba + g, bb + Rs[g]))
    return E


def _bad(N, adj, D):
    """Ordered pairs at distance > D, computed with bitsets. Zero iff diameter <= D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _cost(k, G, R, P, S, D):
    E = _lift_edges(k, G, R, P, S)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return _bad(N, adj, D)


def _anneal(k, G, R, d, D, rng, deadline, iters):
    """Simulated annealing over permutations and voltages. Returns (cost, P, S)."""
    P = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cur = _cost(k, G, R, P, S, D)
    T = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        T = max(0.05, T * 0.996)
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = S[L][i]
            S[L][i] = rng.randrange(G)
            c2 = _cost(k, G, R, P, S, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                S[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]
            c2 = _cost(k, G, R, P, S, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                P[L][a], P[L][b] = P[L][b], P[L][a]
    return cur, P, S


# ----------------------------------------------------------------------------
# Haar hill-climb for small D (secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.78 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
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

    if D <= 4:
        # Small-D secondary family: Haar graphs with a hill-climbed connection set.
        haar_m = d + 1
        misses = 0
        while time.monotonic() < deadline and misses < 6:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                misses = 0
            else:
                misses += 1
            haar_m += 1
    else:
        # Main family for D >= 5: non-cyclic bi-Cayley lifts, annealed, with the
        # target order raised after every success.
        ks = [2, 3, 3, 4, 4, 5, 6]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            # Aim just above the current best order: 2*k*G > best_n.
            G_min = best_n // (2 * k) + 1
            G = G_min + rng.randint(0, 2)
            if G < 2:
                continue
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            R = [[mul(x, s) for x in range(order)] for s in range(order)]
            cur, P, S = _anneal(k, order, R, d, D, rng, deadline, 700)
            if cur == 0:
                E = _lift_edges(k, order, R, P, S)
                consider(2 * k * order, sorted(E))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
