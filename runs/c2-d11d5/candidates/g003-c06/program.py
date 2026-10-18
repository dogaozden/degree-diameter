import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective planes (exact for D = 3, valid for D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: Haar-type bi-Cayley graphs over a single group G of order
# G, with connection set S of size d. A_g ~ B_{g*s} for s in S.
#
# Left multiplication is an automorphism, so the graph is vertex-transitive on
# each side. The diameter check therefore needs only two BFS runs, from A_1 and
# B_1, with depth D. This is exact and costs O(d * G * D) numpy work per step.
#
# A search over the group (cyclic or semidirect Z_m x| Z_k2) and the connection
# set S finds a valid graph with 2G vertices. A gallop plus bisection over G
# finds the largest order it can reach within the stage budget.
# ----------------------------------------------------------------------------

def _divisors_small(n, cap=60):
    return [k for k in range(1, min(n, cap) + 1) if n % k == 0]


def _groups_of_order(n, rng):
    """Candidate (m, k2, r) with m * k2 = n for groups Z_m x| Z_k2, shuffled."""
    out = []
    for k2 in _divisors_small(n):
        m = n // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        cands = {1, m - 1}
        for _ in range(30):
            cands.add(rng.randrange(1, m))
        for r in cands:
            if r % m and math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    rng.shuffle(out)
    return out


def _mult_table(m, k2, r):
    """M[x, y] = x * y in Z_m x| Z_k2, element (a, b) coded as a*k2 + b, identity 0."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return M


def _set_col(nbr, M, inv, G, i, s):
    """Column i of the neighbour table: A_g -> B_{g s}, B_h -> A_{h s^-1}."""
    nbr[:G, i] = G + M[:, s]
    nbr[G:, i] = M[:, inv[s]]


def _unreached_haar(nbr, G, D):
    """Number of (source, vertex) pairs at distance > D, sources A_0 and B_0."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            cand = nbr[frontier].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            seen[cand] = True
            frontier = cand
        total += N - int(np.count_nonzero(seen))
    return total


def _haar_sa(d, D, M, inv, G, rng, deadline, iters, patience):
    """Simulated annealing over S. Returns the list S on success, else None."""
    S = rng.sample(range(G), d)
    nbr = np.empty((2 * G, d), dtype=np.int64)
    for i, s in enumerate(S):
        _set_col(nbr, M, inv, G, i, s)
    cost = _unreached_haar(nbr, G, D)
    c0 = float(max(cost, 1))
    best, last = cost, 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline or t - last > patience:
            break
        temp = max(0.2, 0.05 * c0 * (1.0 - t / iters))
        i = rng.randrange(d)
        old = S[i]
        new = rng.randrange(G)
        if new in S:
            continue
        _set_col(nbr, M, inv, G, i, new)
        S[i] = new
        c2 = _unreached_haar(nbr, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best:
                best, last = cost, t
        else:
            S[i] = old
            _set_col(nbr, M, inv, G, i, old)
    return list(S) if cost == 0 else None


def _probe(d, D, Gp, rng, deadline):
    """Try to find a valid Haar-type graph with group order Gp. Returns (m, k2, r, S) or None."""
    groups = _groups_of_order(Gp, rng)[:6]
    if not groups:
        return None
    attempt = 0
    while time.monotonic() < deadline:
        m, k2, r = groups[attempt % len(groups)]
        attempt += 1
        M = _mult_table(m, k2, r)
        inv = np.argmax(M == 0, axis=1)
        S = _haar_sa(d, D, M, inv, Gp, rng, deadline, 20000, 1500)
        if S is not None:
            return (m, k2, r, S)
    return None


def _haar_stage(d, D, rng, deadline, n0):
    """Gallop then bisect over the group order G. Returns (G, m, k2, r, S) or None."""
    remaining = deadline - time.monotonic()
    per = max(2.0, 0.1 * remaining)

    def probe(g):
        return _probe(d, D, g, rng, min(deadline, time.monotonic() + per))

    lo = max(d + 1, n0 // 2)
    res = probe(lo)
    if res is None:
        return None
    sol = (lo,) + res
    hi = None
    while time.monotonic() < deadline:
        g = max(lo + 1, lo * 5 // 4)
        res = probe(g)
        if res is None:
            hi = g
            break
        lo, sol = g, (g,) + res
    if hi is None:
        return sol
    while hi - lo > max(1, lo // 250) and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        res = probe(mid)
        if res is None:
            hi = mid
        else:
            lo, sol = mid, (mid,) + res
    return sol


def _haar_graph_from(Gp, m, k2, r, S):
    """Build the 2Gp-vertex graph: A_g ~ B_{g s} for s in S."""
    M = _mult_table(m, k2, r)
    edges = []
    for s in S:
        col = (Gp + M[:, s]).tolist()
        edges.extend((a, b) for a, b in enumerate(col))
    return 2 * Gp, edges


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 with k base vertices
# per side (kept from the previous version, used with the leftover budget).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2. Ts[s, g] = g*s and Invs[s, h] = g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    # Exact projective-plane construction; returns immediately for calibration.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # New stage: Haar-type bi-Cayley search over a single group, gallop + bisect.
    if D >= 3 and d >= 2 and time.monotonic() < deadline:
        haar_deadline = start + 0.7 * budget
        sol = _haar_stage(d, D, rng, haar_deadline, best_n)
        if sol is not None:
            n2, e2 = _haar_graph_from(*sol)
            consider(n2, e2)

    # Remaining budget: multi-base bi-Cayley search from the best graph so far.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.1:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
