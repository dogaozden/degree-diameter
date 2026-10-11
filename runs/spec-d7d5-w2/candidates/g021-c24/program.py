import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact baseline: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW BOLD FAMILY: Haar graphs over random groups (one base vertex per side).
#
# Group G = Z_m x| Z_k2 with element (a,b) coded a*k2+b. Pick a connection set
# S of d distinct group elements. The graph has a_g ~ b_{g*s} for s in S, so it
# is bipartite, d-regular, of order 2|G|, and left multiplication is an
# automorphism. Hence every pairwise distance is determined by distances from
# a_e and b_e, and the diameter test reduces to two BFS runs. Simulated
# annealing over S minimises the number of unreached vertices.
# ----------------------------------------------------------------------------

def _group_table(order, rng):
    """Random group of the given order as Z_m x| Z_k2 with m*k2 = order. Returns (G, M, inv)."""
    divs = [k for k in range(1, min(order, 24) + 1)
            if order % k == 0 and order // k >= 2]
    if not divs:
        return None
    k2 = rng.choice(divs)
    m = order // k2
    r = 1
    if k2 > 1 and m > 2:
        for _ in range(200):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return G, M, inv


def _haar_nb(G, M, inv, S):
    """Neighbour table over 2G vertices: index g is a_g, index G+h is b_h."""
    Sarr = np.asarray(S, dtype=np.int64)
    Sinv = inv[Sarr]
    NB = np.empty((2 * G, len(S)), dtype=np.int64)
    NB[:G] = G + M[:, Sarr]
    NB[G:] = M[:, Sinv]
    return NB


def _haar_cost(G, NB, D):
    """Number of vertices not within distance D of a_e or of b_e (0 means diameter <= D)."""
    total = 0
    for src in (0, G):
        vis = np.zeros(2 * G, dtype=bool)
        vis[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = NB[frontier].ravel()
            nxt = nxt[~vis[nxt]]
            if nxt.size == 0:
                break
            nxt = np.unique(nxt)
            vis[nxt] = True
            frontier = nxt
        total += 2 * G - int(vis.sum())
    return total


def _haar_anneal(d, D, G, M, inv, rng, deadline, iters):
    """Anneal a connection set S of size d in G. Returns S with zero cost, or None."""
    if d > G:
        return None
    S = rng.sample(range(G), d)
    NB = _haar_nb(G, M, inv, S)
    cost = _haar_cost(G, NB, D)
    c0 = float(max(cost, 1))
    inS = set(S)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = S[i]
        S[i] = new
        NB2 = _haar_nb(G, M, inv, S)
        c2 = _haar_cost(G, NB2, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            NB = NB2
            inS.discard(old)
            inS.add(new)
        else:
            S[i] = old
    if cost != 0:
        return None
    return S


def _haar_edges(G, M, S):
    """Return (2G, edges) for the Haar graph with connection set S."""
    Sarr = np.asarray(S, dtype=np.int64)
    NBA = G + M[:, Sarr]
    edges = [(g, int(v)) for g in range(G) for v in NBA[g]]
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Previous family (kept as second phase): bi-Cayley lifts over semidirect
# products with k base blocks, layer permutations and simulated annealing.
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
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

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
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
# Bipartition colouring and greedy pair insertion.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
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


def _extend(n, edges, d, D, rng, deadline):
    """Greedy pair insertion: grow the order by 2 per accepted step, keeping validity."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
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
            return True
        return False

    # Exact construction; returns immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (bold): Haar graphs over random groups, growing the group order.
    if D >= 3:
        haar_deadline = start + 0.55 * budget
        lo = max(d + 1, best_n // 2)
        step = 16
        fails = 0
        while time.monotonic() < haar_deadline:
            cand = lo + step
            tab = _group_table(cand, rng)
            if tab is None:
                step = max(1, step // 2)
                continue
            G, M, inv = tab
            attempt_deadline = min(haar_deadline, time.monotonic() + 8.0)
            S = _haar_anneal(d, D, G, M, inv, rng, attempt_deadline, 60000)
            if S is not None and consider(*_haar_edges(G, M, S)):
                lo = cand
                step = min(2 * step, 64)
                fails = 0
            else:
                fails += 1
                if step > 1 and fails >= 2:
                    step //= 2
                    fails = 0

    # Phase 2: bi-Cayley lifts with the earlier bandit search.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    bic_deadline = start + 0.80 * budget
    while time.monotonic() < bic_deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, bic_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 3: greedy pair insertion on the best graph.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
