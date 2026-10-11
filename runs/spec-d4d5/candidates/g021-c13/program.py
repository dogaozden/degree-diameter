"""Bipartite degree-diameter construction: Haar baseline + annealed vertex growth.

Pipeline:
  1. Safe baselines: K_{d,d}, projective plane incidence graph, Haar graphs found by
     hill-climbing the connection set.
  2. Growth: take the best valid graph with N vertices per side, add one vertex per side,
     and repair with simulated annealing. Moves are degree-preserving switches, rewires
     that attach a deficient vertex, and edge additions. Cost = number of vertex pairs at
     distance > D. Each success is validated with lib.is_valid before being kept.
Every returned graph is validated, and the fallback is K_{d,d}.
"""
import math
import random
import time

import lib

_FRAC = 0.78
_SA_CAP_LIMIT = 400


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _haar_hill(d, D, m, rng, deadline, iters):
    if m < d + 1:
        return None
    others = list(range(1, m))

    def cost(S):
        n, e = lib.haar_graph(m, S)
        return lib.bad_pairs(n, e, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        cand = [x for x in others if x not in S]
        if not cand:
            break
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Adjacency representation for growth.
# A-side vertex i has id i (0 <= i < cap); B-side vertex j has id cap + j.
# Only the first N vertices of each side are active.
# ----------------------------------------------------------------------------

def _adj_from(n, edges, cap):
    N = n // 2
    adj = [[] for _ in range(2 * cap)]
    for u, v in edges:
        a, b = (u, v) if u < N else (v, u)
        bb = cap + (b - N)
        adj[a].append(bb)
        adj[bb].append(a)
    return adj


def _to_edges(adj, cap, N):
    edges = []
    for a in range(N):
        for b in adj[a]:
            edges.append((a, N + b - cap))
    return 2 * N, edges


def _add(adj, a, b):
    adj[a].append(b)
    adj[b].append(a)


def _rem(adj, a, b):
    adj[a].remove(b)
    adj[b].remove(a)


def _bad_pairs(adj, act, D, size):
    """Number of unordered active pairs at distance > D."""
    reach = [0] * size
    for v in act:
        reach[v] = 1 << v
    for _ in range(D):
        new = list(reach)
        changed = False
        for v in act:
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            if r != reach[v]:
                new[v] = r
                changed = True
        reach = new
        if not changed:
            break
    T = len(act)
    tot = 0
    for v in act:
        tot += T - reach[v].bit_count()
    return tot // 2


def _anneal(adj, cap, N, d, D, rng, t_end, T0=3.0, T1=0.15):
    """Anneal the N-per-side graph in place. Returns final cost (0 means valid)."""
    act = list(range(N)) + [cap + j for j in range(N)]
    Aids = list(range(N))
    Bids = [cap + j for j in range(N)]
    size = 2 * cap
    cost = _bad_pairs(adj, act, D, size)
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        r = rng.random()
        if r < 0.45:
            # Degree-preserving switch.
            a1 = rng.choice(Aids)
            if not adj[a1]:
                continue
            b1 = rng.choice(adj[a1])
            a2 = rng.choice(Aids)
            if not adj[a2]:
                continue
            b2 = rng.choice(adj[a2])
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            _rem(adj, a1, b1)
            _rem(adj, a2, b2)
            _add(adj, a1, b2)
            _add(adj, a2, b1)
            undo = (0, a1, b1, a2, b2)
        elif r < 0.6:
            # Add an edge between deficient opposite-side vertices.
            dA = [a for a in Aids if len(adj[a]) < d]
            dB = [b for b in Bids if len(adj[b]) < d]
            if not dA or not dB:
                continue
            a = rng.choice(dA)
            b = rng.choice(dB)
            if b in adj[a]:
                continue
            _add(adj, a, b)
            undo = (1, a, b)
        else:
            # Rewire one endpoint of an edge onto a deficient B-vertex.
            a = rng.choice(Aids)
            if not adj[a]:
                continue
            b = rng.choice(adj[a])
            dB = [x for x in Bids if len(adj[x]) < d and x not in adj[a]]
            if not dB:
                continue
            b2 = rng.choice(dB)
            _rem(adj, a, b)
            _add(adj, a, b2)
            undo = (2, a, b, b2)

        new = _bad_pairs(adj, act, D, size)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            if undo[0] == 0:
                _, a1, b1, a2, b2 = undo
                _rem(adj, a1, b2)
                _rem(adj, a2, b1)
                _add(adj, a1, b1)
                _add(adj, a2, b2)
            elif undo[0] == 1:
                _rem(adj, undo[1], undo[2])
            else:
                _, a, b, b2 = undo
                _rem(adj, a, b2)
                _add(adj, a, b)
    return cost


def _grow(adj, N, cap, d, D, rng, deadline, on_success):
    fails = 0
    while fails < 4 and N + 1 < cap:
        now = time.monotonic()
        if now >= deadline:
            break
        span = max(2.0, 0.3 * (deadline - now))
        t_end = min(deadline, now + span)
        trial = [list(x) for x in adj]
        cost = _anneal(trial, cap, N + 1, d, D, rng, t_end)
        if cost == 0:
            adj, N = trial, N + 1
            fails = 0
            on_success(adj, N)
        else:
            fails += 1
    return adj, N


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + _FRAC * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    moore = lib._moore_bound(d, D)
    if D == 2 or best_n >= moore:
        return best_n, best_e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best_n >= moore:
            return best_n, best_e

    # Haar baselines: hill-climb connection sets for growing m.
    haar_end = start + 0.2 * (deadline - start)
    m, miss = d + 1, 0
    while miss < 2 and time.monotonic() < haar_end and m <= moore // 2 + 1:
        S = _haar_hill(d, D, m, rng, haar_end, 150)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)
            miss = 0
        else:
            miss += 1
        m += 1

    # Growth by annealed vertex insertion from the current best graph.
    cap = moore // 2 + 2
    if d >= 3 and D >= 3 and cap <= _SA_CAP_LIMIT and time.monotonic() < deadline:
        try:
            N0 = best_n // 2
            adj = _adj_from(best_n, best_e, cap)

            def on_success(adj_, N_):
                n_, e_ = _to_edges(adj_, cap, N_)
                consider(n_, e_)

            _grow(adj, N0, cap, d, D, rng, deadline, on_success)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
