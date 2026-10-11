import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension (used only on the bi-Cayley parent results).
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
# NEW (bold) construction: single-orbit bi-Cayley graphs over finite groups.
#
# Group G (order G), connection set S of size d. Vertices A_g = g and
# B_h = G + h, with A_g ~ B_{g*s} for s in S. Left multiplication is an
# automorphism that acts transitively on each side, so diameter <= D is
# equivalent to: every vertex is within D of A_e and of B_e.
# Search: simulated annealing over S inside a random group from the
# semidirect family Z_m x| Z_k (including non-abelian groups).
# ----------------------------------------------------------------------------

def _cay_group(G, rng):
    """Return (m, k, r) with m*k = G describing Z_m x| Z_k, or None."""
    divs = [k for k in range(1, min(G, 60) + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(100):
        k = rng.choice(divs)
        m = G // k
        if k == 1:
            return (m, 1, 1)
        if rng.random() < 0.2:
            return (m, k, 1)  # direct product
        if m < 3:
            continue
        for _ in range(100):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                return (m, k, c)
    return None


def _cay_tables(m, k, r):
    """Return (G, Ts, sinv): Ts[s, g] = g*s, sinv[s] = index of s^{-1}."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    # M[g1, g2] = g1 * g2 with (a,b)(c,e) = (a + r^b c, b + e).
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    Ts = np.ascontiguousarray(M.T)
    sinv = np.argmax(M == 0, axis=1).astype(np.int64)
    return G, Ts, sinv


def _cay_set_row(nbr, j, s, G, Ts, sinv):
    """Write row j of the neighbour table for connection element s."""
    nbr[j, :G] = G + Ts[s]           # A_g -> B_{g*s}
    nbr[j, G:] = Ts[sinv[s]]         # B_h -> A_{h*s^{-1}}


def _cay_unreached(nbr, src, D, N):
    """Number of vertices not within distance D of src."""
    seen = np.zeros(N, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(D):
        nxt = nbr[:, front].ravel()
        nxt = np.unique(nxt[~seen[nxt]])
        if nxt.size == 0:
            break
        seen[nxt] = True
        front = nxt
    return N - int(seen.sum())


def _cay_cost(nbr, G, D, N):
    return _cay_unreached(nbr, 0, D, N) + _cay_unreached(nbr, G, D, N)


def _cay_anneal(d, D, G, Ts, sinv, rng, deadline, iters):
    """Anneal a connection set S of size d; return S (list) or None."""
    N = 2 * G
    S = rng.sample(range(G), d)
    nbr = np.empty((d, N), dtype=np.int64)
    for j, s in enumerate(S):
        _cay_set_row(nbr, j, s, G, Ts, sinv)
    cost = _cay_cost(nbr, G, D, N)
    t0 = max(1.0, 0.05 * cost)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 127) == 0 and time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[j]
        S[j] = new
        _cay_set_row(nbr, j, new, G, Ts, sinv)
        c2 = _cay_cost(nbr, G, D, N)
        temp = max(0.2, t0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[j] = old
            _cay_set_row(nbr, j, old, G, Ts, sinv)
    return list(S) if cost == 0 else None


def _cay_edges(S, G, Ts):
    """Edge list of the bi-Cayley graph for connection set S."""
    edges = []
    for s in S:
        row = Ts[s].tolist()
        edges.extend((g, G + row[g]) for g in range(G))
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Parent family (kept as a fallback search): bi-Cayley lifts with base size k.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b)."""
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
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, optimal for D = 2
    if d == 2:
        n = 2 * D  # even cycle C_{2D} has diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} (valid for D >= 2).
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    moore = lib._moore_bound(d, D)
    lo_base = max(d, moore // 6)
    hi_cap = min(moore // 2, 3000)

    # Phase A (bold): single-orbit bi-Cayley search over non-abelian groups.
    cay_deadline = start + 0.45 * budget
    while time.monotonic() < cay_deadline:
        lo = max(lo_base, best_n // 2 + 1)
        if lo > hi_cap:
            break
        G = rng.randint(lo, min(hi_cap, lo + 60))
        grp = _cay_group(G, rng)
        if grp is None:
            continue
        m, k, r = grp
        Gt, Ts, sinv = _cay_tables(m, k, r)
        S = _cay_anneal(d, D, Gt, Ts, sinv, rng, cay_deadline, 4000)
        if S is not None:
            n, e = _cay_edges(S, Gt, Ts)
            consider(n, e)

    # Phase B (fallback): bandit over bi-Cayley lifts with base size k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
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

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
