import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Local search on bipartite d-regular graphs (A = 0..M-1, B = 0..M-1).
#
# Moves are edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep every
# degree and the bipartition. Growth inserts one new A-vertex and one new
# B-vertex by splitting d edges, then annealing repairs the diameter.
# ----------------------------------------------------------------------------

def _ball_cost(M, E, D):
    """Ordered vertex pairs at distance > D in the bipartite graph given by edge list E."""
    N = 2 * M
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(M + b)
        adj[M + b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        if nxt == reach:
            break
        reach = nxt
    return sum(N - r.bit_count() for r in reach)


def _anneal(M, E, S, D, budget, T0, T1, rng, deadline):
    """Simulated annealing with edge switches. E is a list of (a, b); S mirrors it as a set."""
    cur = _ball_cost(M, E, D)
    L = len(E)
    for it in range(budget):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / budget)
        i = rng.randrange(L)
        j = rng.randrange(L)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        new = _ball_cost(M, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
            cur = new
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return cur


def _insert(M, E, S, d, rng):
    """Add new A-vertex M and B-vertex M, each of degree d, by splitting d edges with distinct ends."""
    if len(E) < d:
        return False
    idx = None
    for _ in range(300):
        cand = rng.sample(range(len(E)), d)
        if len({E[i][0] for i in cand}) == d and len({E[i][1] for i in cand}) == d:
            idx = cand
            break
    if idx is None:
        return False
    for i in idx:
        a, b = E[i]
        S.discard((a, b))
        E[i] = (M, b)
        S.add((M, b))
        E.append((a, M))
        S.add((a, M))
    return True


def _local_search(d, D, deadline, rng, consider):
    M = d
    E = [(a, b) for a in range(d) for b in range(d)]  # K_{d,d}
    S = set(E)
    saved = (M, list(E), set(S))
    stuck = 0
    while time.monotonic() < deadline:
        if _ball_cost(M, E, D) == 0:
            saved = (M, list(E), set(S))
            consider(2 * M, [(a, M + b) for a, b in E])
            if not _insert(M, E, S, d, rng):
                break
            M += 1
            stuck = 0
        else:
            _anneal(M, E, S, D, 800, 4.0, 0.4, rng, deadline)
            stuck += 1
            if stuck >= 25:
                M, E0, S0 = saved
                E = list(E0)
                S = set(S0)
                stuck = 0


# ----------------------------------------------------------------------------
# Secondary family: bi-Cayley voltage lifts over Z_m x| Z_k2 (annealed).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(60):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        r = 1
        if k2 > 1:
            cands = [x for x in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


def _lift_cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _lift_run(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s, old_p = darts[idx][2], perms[idx]
            darts[idx][2] = rng.randrange(G)
            perms[idx] = [mul(g, darts[idx][2]) for g in range(G)]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 - cost <= 0 or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 - cost <= 0 or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_phase(d, D, deadline, rng, consider, best):
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = max(1, best[0] // (2 * k))
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _lift_run(d, D, k, order, mul, rng, deadline, 400)
        if res is not None:
            consider(res[0], res[1])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    local_deadline = start + 0.5 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = [n0, e0]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Projective plane incidence graph (diameter 3) for D >= 3.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n1, e1 = lib.projective_plane_incidence(q)
                consider(n1, e1)
                break

    # Main family: edge-switch local search with vertex insertion.
    _local_search(d, D, local_deadline, rng, consider)

    # Secondary family: annealed voltage lifts for the remaining time.
    _lift_phase(d, D, deadline, rng, consider, best)

    if not lib.is_valid(best[0], best[1], d, D):
        n0, e0 = lib.haar_graph(d, range(d))
        return n0, e0
    return best[0], best[1]
