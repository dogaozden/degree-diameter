import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Phase 1: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Each layer pairs A_i with B_{layers[l][i]} through voltage s, so every layer
# is a permutation and the graph is d-regular and bipartite.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = _POP[:256]
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
    """Greedy pair insertion with validity check (regularity and bipartiteness kept)."""
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
# Phase 2 (new construction): grow a regular bipartite graph by pair insertion,
# then repair it with degree-preserving 2-switches that minimise the number of
# vertex pairs at distance > D. Distances are computed on bit-packed reach
# matrices with numpy, so one cost evaluation is a few milliseconds.
# ----------------------------------------------------------------------------

def _init_reach(n):
    W = (n + 63) // 64
    eye = np.zeros((n, W * 64), dtype=np.uint8)
    idx = np.arange(n)
    eye[idx, idx] = 1
    return np.packbits(eye, axis=1, bitorder="little").view(np.uint64).copy()


def _bad_pairs(nbr, D, init):
    """Number of unordered vertex pairs at distance > D (0 means valid diameter)."""
    n, d = nbr.shape
    reach = init
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - total) // 2


def _kd_arrays(d):
    nbr = np.empty((2 * d, d), dtype=np.int64)
    for a in range(d):
        nbr[a] = np.arange(d, 2 * d)
        nbr[d + a] = np.arange(d)
    color = np.array([0] * d + [1] * d, dtype=np.int8)
    return nbr, color


def _to_arrays(n, edges, d):
    color = _two_color(n, edges)
    if color is None:
        return None
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return None
    return np.array(adj, dtype=np.int64), np.array(color, dtype=np.int8)


def _nbr_edges(nbr):
    edges = []
    for u in range(nbr.shape[0]):
        for v in nbr[u].tolist():
            if u < v:
                edges.append((u, v))
    return edges


def _grow(nbr, color, d, rng):
    """Insert one pair (x in colour 0, y in colour 1) keeping regularity and bipartiteness."""
    n = nbr.shape[0]
    edges = []
    for a in np.flatnonzero(color == 0).tolist():
        for b in nbr[a].tolist():
            edges.append((a, b))
    rng.shuffle(edges)
    chosen = []
    ua, ub = set(), set()
    for a, b in edges:
        if len(chosen) == d - 1:
            break
        if a in ua or b in ub:
            continue
        chosen.append((a, b))
        ua.add(a)
        ub.add(b)
    if len(chosen) < d - 1:
        return None
    x, y = n, n + 1
    new = np.empty((n + 2, d), dtype=np.int64)
    new[:n] = nbr
    for a, b in chosen:
        new[a][new[a] == b] = y
        new[b][new[b] == a] = x
    new[x, :d - 1] = [b for _, b in chosen]
    new[x, d - 1] = y
    new[y, :d - 1] = [a for a, _ in chosen]
    new[y, d - 1] = x
    nc = np.concatenate([color, np.array([0, 1], dtype=color.dtype)])
    return new, nc


def _anneal(nbr, color, D, rng, deadline, iters):
    """2-switch annealing on bad-pair count. Modifies nbr in place; returns final cost."""
    n, d = nbr.shape
    init = _init_reach(n)
    Al = np.flatnonzero(color == 0).tolist()
    cost = _bad_pairs(nbr, D, init)
    c0 = float(max(cost, 1))
    it = 0
    while cost > 0 and it < iters and time.monotonic() < deadline:
        temp = max(0.5, 0.02 * c0 * (1.0 - it / iters))
        it += 1
        a1 = Al[rng.randrange(len(Al))]
        a2 = Al[rng.randrange(len(Al))]
        if a1 == a2:
            continue
        s1 = rng.randrange(d)
        s2 = rng.randrange(d)
        b1 = int(nbr[a1, s1])
        b2 = int(nbr[a2, s2])
        if b1 == b2 or (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        saved = {}
        for v in (a1, a2, b1, b2):
            if v not in saved:
                saved[v] = nbr[v].copy()
        nbr[a1, s1] = b2
        nbr[a2, s2] = b1
        i1 = int(np.flatnonzero(nbr[b1] == a1)[0])
        nbr[b1, i1] = a2
        i2 = int(np.flatnonzero(nbr[b2] == a2)[0])
        nbr[b2, i2] = a1
        c2 = _bad_pairs(nbr, D, init)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            for v, row in saved.items():
                nbr[v] = row
    return cost


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    p1_deadline = start + 0.60 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D == 2 or d < 3:
        return best

    # ---- Phase 1: bi-Cayley lift search, then greedy pair insertion. ----
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    search_deadline = start + 0.85 * (p1_deadline - start)
    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best[0]:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    try:
        n2, e2 = _extend(best[0], best[1], d, D, rng, p1_deadline)
        if n2 > best[0]:
            consider(n2, e2)
    except Exception:
        pass

    # ---- Phase 2: grow by pair insertion and repair by annealing. ----
    conv = _to_arrays(best[0], best[1], d)
    if conv is None:
        nbr, color = _kd_arrays(d)
        best_base = lib.haar_graph(d, range(d))
    else:
        nbr, color = conv
        best_base = best
    best_nbr, best_color = nbr, color
    s = 1
    try:
        while time.monotonic() < deadline - 1.0:
            cur_nbr = best_nbr.copy()
            cur_color = best_color.copy()
            grown = 0
            for _ in range(s):
                g = _grow(cur_nbr, cur_color, d, rng)
                if g is None:
                    break
                cur_nbr, cur_color = g
                grown += 1
            if grown == 0:
                break
            cost = _anneal(cur_nbr, cur_color, D, rng, deadline, 800)
            if cost == 0:
                best_nbr, best_color = cur_nbr, cur_color
                s = min(2 * s, 32)
            else:
                s = max(1, s // 2)
    except Exception:
        pass

    if best_nbr.shape[0] > best[0]:
        consider(int(best_nbr.shape[0]), _nbr_edges(best_nbr))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
