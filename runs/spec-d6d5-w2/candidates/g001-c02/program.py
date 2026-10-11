import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d}, projective-plane incidence graphs, Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _k_dd(d):
    """K_{d,d}: diameter 2, degree d, valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def _pg_candidate(d):
    """PG(2, q) incidence graph with q = d - 1: degree d, diameter 3, meets the Moore bound."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 (q a prime power >= 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs over nonabelian metacyclic groups.
#
# Vertices A_g = g and B_h = G + h, with g, h in the group H of order G.
# Edges A_g -- B_{g*s} for each s in a connection set S of d distinct elements.
# Every vertex has degree d, and the graph is bipartite by construction.
#
# Left multiplication by H is an automorphism of the graph, so the diameter is
# max(ecc(A_e), ecc(B_e)). Two BFS runs therefore decide validity exactly.
# Nonabelian groups are preferred because abelian groups have polynomial
# ball growth, which is far too slow for diameter 5.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random nonabelian semidirect product Z_m x| Z_k of order G; cyclic if no such group exists."""
    opts = []
    for k in range(2, 13):
        if G % k:
            continue
        m = G // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                opts.append((m, k, r))
    if opts:
        m, k, r = rng.choice(opts)
    else:
        m, k, r = G, 1, 1
    order, mul, inv = lib.semidirect_group(m, k, r)
    return order, mul, inv


def _make_getR(G, mul):
    """Cached right-multiplication permutations: getR(x)[g] = g * x."""
    cache = {}

    def getR(x):
        R = cache.get(x)
        if R is None:
            R = [mul(g, x) for g in range(G)]
            cache[x] = R
        return R

    return getR


def _cost(G, D, S, getR, inv):
    """Total number of vertices unreached within D steps from A_e and from B_e (zero iff valid)."""
    Rs = [getR(s) for s in S]
    Ri = [getR(inv(s)) for s in S]
    N = 2 * G
    total = 0
    for root in (0, G):
        seen = bytearray(N)
        seen[root] = 1
        frontier = [root]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for R in Rs:
                        v = G + R[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for R in Ri:
                        v = R[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _anneal(G, d, D, getR, inv, rng, iters, deadline):
    """Simulated annealing over connection sets of d distinct elements. Returns S or None."""
    if G <= d:
        return None
    S = rng.sample(range(G), d)
    cost = _cost(G, D, S, getR, inv)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(G, D, S, getR, inv)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
        T = max(0.25, T * 0.995)
    return S if cost == 0 else None


def _edges(G, S, getR):
    """Edge list of the bi-Cayley graph for connection set S."""
    E = []
    for s in S:
        R = getR(s)
        for g in range(G):
            E.append((g, G + R[g]))
    return 2 * G, E


def _search(d, D, deadline, rng, state):
    """Ratchet the group order upward. state['n'] and state['g'] hold the best valid graph so far."""
    moore = lib.moore_bound(d, D)
    if state['n'] >= moore:
        return
    base = max(d + 2, int(0.3 * moore / 2))
    best_G = max(base, state['n'] // 2 + 1) - 1
    while time.monotonic() < deadline:
        G = best_G + 1 + rng.randrange(4)
        try:
            order, mul, inv = _sample_group(G, rng)
            getR = _make_getR(order, mul)
            S = _anneal(order, d, D, getR, inv, rng, 600, deadline)
        except ValueError:
            continue
        if S is None:
            continue
        n, E = _edges(order, S, getR)
        if n > state['n'] and lib.is_valid(n, E, d, D):
            state['n'] = n
            state['g'] = (n, E)
            best_G = order


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = _k_dd(d)
    best_n = best[0]

    if D >= 3:
        for cand in (_pg_candidate(d), _araujo_candidate(d)):
            if cand is not None and cand[0] > best_n and lib.is_valid(cand[0], cand[1], d, D):
                best, best_n = cand, cand[0]

    if D >= 3 and time.monotonic() < deadline:
        state = {'n': best_n, 'g': best}
        try:
            _search(d, D, deadline, rng, state)
        except Exception:
            pass
        best_n, best = state['n'], state['g']

    if not lib.is_valid(best[0], best[1], d, D):
        best = _k_dd(d)
    return best
