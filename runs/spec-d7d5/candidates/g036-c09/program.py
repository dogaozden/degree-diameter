import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Small helpers.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """Return the 2-colouring of the graph as a list, or None if it is not bipartite."""
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


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent's lift search).
# ----------------------------------------------------------------------------

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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over bi-Cayley lifts with stagnation cutoff. Returns (n, edges) or None."""
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
# NEW: double-edge-swap annealing on an explicit d-regular bipartite graph,
# plus vertex-pair insertion by edge splitting.
#
# Insertion: pick d disjoint edges (a_i, b_i) with a_i on side 0 and b_i on
# side 1. Delete them, add x (side 0) joined to all b_i and y (side 1) joined
# to all a_i. Every old vertex keeps degree d, and x and y get degree d. The
# result is again d-regular and bipartite, with 2 more vertices, but its
# diameter is usually broken.
#
# Repair: double-edge swaps (a,b),(c,e) -> (a,e),(c,b) on side-0 vertices a,c.
# They keep the graph d-regular and bipartite. Cost is the number of ordered
# unreached pairs, computed with a packed-bit numpy reachability sweep.
# ----------------------------------------------------------------------------

def _regular_nbr(n, edges, d):
    """Return an (n, d) neighbour array if the graph is d-regular, else None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    return np.array(adj, dtype=np.int64)


def _edges_from(nbr):
    return [(u, int(v)) for u in range(nbr.shape[0]) for v in nbr[u] if u < int(v)]


def _insert_pair(nbr, color, d, rng):
    """Insert two vertices by edge splitting; return (new_nbr, new_color) or (None, None)."""
    n = nbr.shape[0]
    order = list(range(n))
    rng.shuffle(order)
    usedA, usedB, pairs = set(), set(), []
    for a in order:
        if len(pairs) == d:
            break
        if color[a] != 0 or a in usedA:
            continue
        opts = [int(b) for b in nbr[a] if int(b) not in usedB]
        if not opts:
            continue
        b = rng.choice(opts)
        usedA.add(a)
        usedB.add(b)
        pairs.append((a, b))
    if len(pairs) < d:
        return None, None
    new = np.empty((n + 2, d), dtype=np.int64)
    new[:n] = nbr
    x, y = n, n + 1
    for a, b in pairs:
        ia = int(np.flatnonzero(new[a] == b)[0])
        new[a, ia] = y
        ib = int(np.flatnonzero(new[b] == a)[0])
        new[b, ib] = x
    new[x] = [b for _, b in pairs]
    new[y] = [a for a, _ in pairs]
    newcol = np.concatenate([np.asarray(color, dtype=np.int64), np.array([0, 1], dtype=np.int64)])
    return new, newcol


def _cost(nbr, D):
    """Number of ordered unreached vertex pairs (0 means diameter <= D)."""
    n = nbr.shape[0]
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    cnt = int(_POP8[reach.view(np.uint8)].sum())
    return n * n - cnt


def _anneal(nbr, color, d, D, rng, deadline, iters):
    """Double-edge-swap annealing until diameter <= D. Mutates nbr; returns True on success."""
    n = nbr.shape[0]
    A = np.flatnonzero(np.asarray(color) == 0)
    if A.size < 2:
        return False
    cost = _cost(nbr, D)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.02 * c0 * (1.0 - t / iters))
        a = int(A[rng.randrange(A.size)])
        c = int(A[rng.randrange(A.size)])
        if a == c:
            continue
        p = rng.randrange(d)
        q = rng.randrange(d)
        b = int(nbr[a, p])
        e = int(nbr[c, q])
        if b == e or (nbr[a] == e).any() or (nbr[c] == b).any():
            continue
        ib = int(np.flatnonzero(nbr[b] == a)[0])
        ie = int(np.flatnonzero(nbr[e] == c)[0])
        nbr[a, p] = e
        nbr[c, q] = b
        nbr[b, ib] = c
        nbr[e, ie] = a
        c2 = _cost(nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            nbr[a, p] = b
            nbr[c, q] = e
            nbr[b, ib] = a
            nbr[e, ie] = c
    return cost == 0


def _grow(best, d, D, rng, deadline, consider):
    """Repeatedly insert vertex pairs into a regular graph and repair; keep successes."""
    n, edges = best
    nbr = _regular_nbr(n, edges, d)
    if nbr is None:
        return
    color = _bipartition(n, lib.adjacency(n, edges))
    if color is None:
        return
    cur_nbr, cur_color = nbr, np.asarray(color, dtype=np.int64)
    while time.monotonic() < deadline - 0.5:
        tr_nbr, tr_color = _insert_pair(cur_nbr, cur_color, d, rng)
        if tr_nbr is None:
            break
        slice_end = min(deadline, time.monotonic() + 4.0)
        if _anneal(tr_nbr, tr_color, d, D, rng, slice_end, 3000):
            cur_nbr, cur_color = tr_nbr, tr_color
            consider(tr_nbr.shape[0], _edges_from(tr_nbr))


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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: lift search (about 55% of the budget).
    lift_deadline = start + 0.55 * budget
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: vertex-pair insertion with double-edge-swap repair.
    try:
        _grow(best, d, D, rng, final_deadline, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
