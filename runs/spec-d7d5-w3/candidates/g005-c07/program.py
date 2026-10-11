import math
import random
import sys
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


# ----------------------------------------------------------------------------
# Phase A: bi-Cayley lifts over semidirect products Z_m x| Z_k2 (structured
# search). It produces a seed graph, which phase B then grows and repairs.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
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
    """Simulated annealing over bi-Cayley voltages. Returns (n, edges) or None."""
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
# Phase B (new): plain d-regular bipartite graphs, not group-invariant.
#
# The seed graph is split into d perfect matchings ("layers"). Each layer is a
# bijection A -> B. Then:
#   * grow: add one vertex to each side, rewiring one edge per layer
#     (degree stays exactly d, the graph stays simple and bipartite);
#   * repair: simulated annealing with degree-preserving 2-switches inside a
#     layer, minimising the number of ordered vertex pairs at distance > D.
# Reachability is tracked with packed uint64 bitsets (numpy).
# ----------------------------------------------------------------------------

def _regular_bipartite_parts(n, edges, d):
    """Return (h, adjA) if the graph is d-regular bipartite with equal sides, else None.

    adjA[a] lists the B-side indices adjacent to A-side index a (both sides 0..h-1).
    """
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, adj)
    if color is None:
        return None
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if not A or len(A) != len(B):
        return None
    ib = {v: i for i, v in enumerate(B)}
    adjA = [[ib[w] for w in adj[v]] for v in A]
    return len(A), adjA


def _perfect_matching(h, adjs):
    """Kuhn's algorithm on the bipartite graph adjs (A index -> list of B indices)."""
    matchA = [-1] * h
    matchB = [-1] * h
    for a in range(h):
        for b in adjs[a]:
            if matchB[b] == -1:
                matchA[a] = b
                matchB[b] = a
                break

    def augment(a, seen):
        for b in adjs[a]:
            if not seen[b]:
                seen[b] = True
                if matchB[b] == -1 or augment(matchB[b], seen):
                    matchA[a] = b
                    matchB[b] = a
                    return True
        return False

    for a in range(h):
        if matchA[a] == -1:
            if not augment(a, [False] * h):
                return None
    return matchA


def _decompose(h, adjA, d):
    """Split a d-regular bipartite graph into d perfect matchings (as numpy arrays)."""
    rem = [list(x) for x in adjA]
    perms = []
    for _ in range(d):
        pm = _perfect_matching(h, rem)
        if pm is None:
            return None
        perms.append(np.array(pm, dtype=np.int64))
        for a in range(h):
            rem[a].remove(pm[a])
    return perms


def _invert(h, perms):
    invs = []
    ar = np.arange(h, dtype=np.int64)
    for p in perms:
        iv = np.empty(h, dtype=np.int64)
        iv[p] = ar
        invs.append(iv)
    return invs


def _build_nbr(h, perms, invs, d):
    nbr = np.empty((d, 2 * h), dtype=np.int64)
    for l in range(d):
        nbr[l, :h] = h + perms[l]
        nbr[l, h:] = invs[l]
    return nbr


def _make_M(H, perms):
    """M[a, b] = number of layers joining A-index a to B-index b (0 or 1 for a simple graph)."""
    M = np.zeros((H, H), dtype=np.int16)
    ar = np.arange(H)
    for p in perms:
        M[ar, p] += 1
    return M


def _cost(h, nbr, D):
    """Return (ordered unreached pairs, array of rows that are not fully reached)."""
    N = 2 * h
    W = (N + 63) // 64
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    pc = _POP8[reach.view(np.uint8)].sum(axis=1)
    cost = N * N - int(pc.sum())
    bad = np.flatnonzero(pc < N)
    return cost, bad


def _anneal(h, perms, invs, M, nbr, d, D, rng, cost, bad, deadline):
    """Degree-preserving 2-switch annealing. Returns the final cost (0 means valid)."""
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0, T1 = 6.0, 0.3
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - start) / span)
        l = rng.randrange(d)
        pm = perms[l]
        iv = invs[l]
        if bad.size and rng.random() < 0.5:
            v = int(bad[rng.randrange(bad.size)])
            a1 = v if v < h else int(iv[v - h])
        else:
            a1 = rng.randrange(h)
        a2 = rng.randrange(h)
        if a1 == a2:
            continue
        b1 = int(pm[a1])
        b2 = int(pm[a2])
        if M[a1, b2] or M[a2, b1]:
            continue
        # Apply the switch: a1-b2 and a2-b1 replace a1-b1 and a2-b2.
        pm[a1] = b2
        pm[a2] = b1
        iv[b1] = a2
        iv[b2] = a1
        nbr[l, a1] = h + b2
        nbr[l, a2] = h + b1
        nbr[l, h + b1] = a2
        nbr[l, h + b2] = a1
        M[a1, b1] -= 1
        M[a2, b2] -= 1
        M[a1, b2] += 1
        M[a2, b1] += 1
        c2, bad2 = _cost(h, nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, bad = c2, bad2
        else:
            pm[a1] = b1
            pm[a2] = b2
            iv[b1] = a1
            iv[b2] = a2
            nbr[l, a1] = h + b1
            nbr[l, a2] = h + b2
            nbr[l, h + b1] = a1
            nbr[l, h + b2] = a2
            M[a1, b1] += 1
            M[a2, b2] += 1
            M[a1, b2] -= 1
            M[a2, b1] -= 1
    return cost


def _grow(h, perms, invs, d, rng):
    """Add one vertex per side. Layer l moves edge (a_l, b_l) to (a_l, B') and (A', b_l)."""
    a_list = None
    bs = None
    for _ in range(200):
        cand_a = rng.sample(range(h), d)
        cand_b = [int(perms[l][cand_a[l]]) for l in range(d)]
        if len(set(cand_b)) == d:
            a_list, bs = cand_a, cand_b
            break
    if a_list is None:
        return None
    H = h + 1
    new_p, new_i = [], []
    for l in range(d):
        p = np.empty(H, dtype=np.int64)
        p[:h] = perms[l]
        p[h] = bs[l]
        p[a_list[l]] = h
        iv = np.empty(H, dtype=np.int64)
        iv[:h] = invs[l]
        iv[h] = a_list[l]
        iv[bs[l]] = h
        new_p.append(p)
        new_i.append(iv)
    return new_p, new_i, H


def _edges_of(h, perms):
    return [(a, h + int(perms[l][a])) for l in range(len(perms)) for a in range(h)]


def _grow_search(h, perms, invs, d, D, rng, deadline, consider):
    """Repeatedly grow the valid graph by one vertex per side and repair it by annealing."""
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            return
        slice_end = now + min(remaining, max(3.0, 0.4 * remaining))
        g = _grow(h, perms, invs, d, rng)
        if g is None:
            continue
        p2, i2, H = g
        M = _make_M(H, p2)
        nbr = _build_nbr(H, p2, i2, d)
        cost, bad = _cost(H, nbr, D)
        cost = _anneal(H, p2, i2, M, nbr, d, D, rng, cost, bad, slice_end)
        if cost == 0:
            edges = _edges_of(H, p2)
            if lib.is_valid(2 * H, edges, d, D):
                consider(2 * H, edges)
                h, perms, invs = H, p2, i2


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, time_limit - 6.0)
    deadline = start + budget
    rng = random.Random(seed)
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    # Phase A: structured bi-Cayley search for about half the budget.
    phase_a_deadline = start + 0.5 * budget
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < phase_a_deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, phase_a_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase B: grow the best regular bipartite graph and repair by annealing.
    if D >= 3 and d >= 2 and time.monotonic() < deadline - 1.0:
        try:
            reg = _regular_bipartite_parts(best_n, best[1], d)
            if reg is not None:
                h, adjA = reg
                perms = _decompose(h, adjA, d)
                if perms is not None:
                    invs = _invert(h, perms)
                    _grow_search(h, perms, invs, d, D, rng, deadline, consider)
        except (RecursionError, ValueError, IndexError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
