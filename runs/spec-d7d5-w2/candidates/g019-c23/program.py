import itertools
import math
import random
import time

import numpy as np

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


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent search, kept as
# the main fallback engine).
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
# Bipartition colouring, greedy pair insertion (checked).
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
    """Greedy pair insertion; every accepted step passes lib.is_valid."""
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
# Shared state: best valid graph so far.
# ----------------------------------------------------------------------------

def _consider(st, d, D, n, e):
    if n > st["n"] and lib.is_valid(n, e, d, D):
        st["best"] = (n, e)
        st["n"] = n


def _bicayley_search(d, D, rng, st, until):
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < until:
        k = pick_k()
        base = st["n"] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= st["n"]:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, until, 4000)
        if res is not None:
            wins[k] += 1
            _consider(st, d, D, res[0], res[1])


# ----------------------------------------------------------------------------
# Bold construction for d=7, D=5: pair insertion into a regular bipartite
# graph (no validity check), followed by double-edge-swap annealing whose cost
# is the number of ordered vertex pairs at distance > D (bitset BFS).
# Every switch keeps the graph d-regular and bipartite, so only the diameter
# has to be repaired. A result is accepted only if lib.is_valid passes.
# ----------------------------------------------------------------------------

_SLICE = 10.0


def _bad(N, nbr, D):
    """Number of ordered vertex pairs at distance > D in the regular graph given by nbr (N x d)."""
    W = (N + 63) // 64
    idx = np.arange(N)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    pop = int(_POP8[reach.view(np.uint8)].sum())
    return N * N - pop


def _insert_pair(n, nbr, color, d, rng):
    """Remove d-1 edges (a,b) with distinct a's and b's, add x (side 0) ~ all b's and y (side 1) ~ all a's, x ~ y."""
    A = [v for v in range(n) if color[v] == 0]
    rng.shuffle(A)
    used_b = set()
    picks = []
    for a in A:
        if len(picks) == d - 1:
            break
        s = rng.randrange(d)
        b = int(nbr[a, s])
        if b in used_b:
            continue
        used_b.add(b)
        picks.append((a, s, b))
    if len(picks) < d - 1:
        return None
    x, y = n, n + 1
    new = np.empty((n + 2, d), dtype=np.int64)
    new[:n] = nbr
    new[x, :d - 1] = [b for _, _, b in picks]
    new[x, d - 1] = y
    new[y, :d - 1] = [a for a, _, _ in picks]
    new[y, d - 1] = x
    for a, s, b in picks:
        t = int(np.flatnonzero(nbr[b] == a)[0])
        new[a, s] = y
        new[b, t] = x
    col = list(color) + [0, 1]
    return n + 2, new, col


def _sa(N, nbr, color, d, D, deadline, rng):
    """Double-edge-swap annealing on bad-pair count. Returns (best_cost, best_nbr)."""
    A = [v for v in range(N) if color[v] == 0]
    cost = _bad(N, nbr, D)
    best_cost = cost
    best_nbr = nbr.copy()
    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.5, 4.0 * (1.0 - (now - t_begin) / span))
        a1 = A[rng.randrange(len(A))]
        a2 = A[rng.randrange(len(A))]
        if a1 == a2:
            continue
        s1 = rng.randrange(d)
        s2 = rng.randrange(d)
        b1 = int(nbr[a1, s1])
        b2 = int(nbr[a2, s2])
        if b1 == b2:
            continue
        if (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
            continue
        t1 = int(np.flatnonzero(nbr[b1] == a1)[0])
        t2 = int(np.flatnonzero(nbr[b2] == a2)[0])
        nbr[a1, s1] = b2
        nbr[a2, s2] = b1
        nbr[b1, t1] = a2
        nbr[b2, t2] = a1
        c2 = _bad(N, nbr, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_nbr[:] = nbr
        else:
            nbr[a1, s1] = b1
            nbr[a2, s2] = b2
            nbr[b1, t1] = a1
            nbr[b2, t2] = a2
    return best_cost, best_nbr


def _edges_from(n, nbr, color):
    return [(a, int(b)) for a in range(n) if color[a] == 0 for b in nbr[a]]


def _bold_search(d, D, rng, st, until):
    n, e = st["best"]
    adj = lib.adjacency(n, e)
    if not all(len(a) == d for a in adj):
        return
    color = _two_color(n, e)
    if color is None:
        return
    nbr = np.array(adj, dtype=np.int64)
    while time.monotonic() < until - 0.5:
        ins = _insert_pair(n, nbr, color, d, rng)
        if ins is None:
            break
        n2, nb2, col2 = ins
        slice_end = min(until, time.monotonic() + _SLICE)
        cost, best_nb = _sa(n2, nb2, col2, d, D, slice_end, rng)
        if cost == 0:
            edges = _edges_from(n2, best_nb, col2)
            if lib.is_valid(n2, edges, d, D):
                _consider(st, d, D, n2, edges)
                if st["n"] == n2:
                    n, nbr, color = n2, best_nb, col2


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    haar = lib.haar_graph(d, range(d))
    st = {"best": haar, "n": haar[0]}

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            _consider(st, d, D, pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return st["best"]

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            _consider(st, d, D, gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return st["best"]

    if d == 7 and D == 5:
        # Bold path: a short parent-style search first, then insertion + annealing.
        _bicayley_search(d, D, rng, st, start + 0.30 * budget)
        _bold_search(d, D, rng, st, deadline)
    else:
        _bicayley_search(d, D, rng, st, start + 0.85 * budget)

    try:
        n2, e2 = _extend(st["n"], st["best"][1], d, D, rng, deadline)
        if n2 > st["n"]:
            _consider(st, d, D, n2, e2)
    except Exception:
        pass

    best = st["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
