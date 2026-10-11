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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (simulated annealing).
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
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
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
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


def _unreached_blocks(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages, layer swaps and defect-targeted moves. Returns (n, edges) or None."""
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
    cost = _unreached_blocks(k, N, reach) + _PENALTY * dupcount()
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
            c2 = _unreached_blocks(k, N, r2) + _PENALTY * dupcount()
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
        c2 = _unreached_blocks(k, N, r2) + _PENALTY * dupcount()
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
# NEW: degree-preserving 2-switch annealing after pair insertion.
#
# Insert a pair (x, y) into a d-regular bipartite graph: x (side A) takes the
# B-ends of d-1 removed edges, y (side B) takes their A-ends, and x ~ y. The graph
# stays d-regular and bipartite, but may now violate the diameter bound. Then
# anneal with bipartite 2-switches (a1 b1, a2 b2) -> (a1 b2, a2 b1), which keep
# every degree fixed, to drive the number of unreached ordered pairs to zero.
# Reachability is a bit-packed boolean matrix, updated by row-gathers over the
# neighbour table.
# ----------------------------------------------------------------------------

def _unreached_pairs(NB, n, D, R0):
    """Number of ordered pairs (v, w) with dist(v, w) > D, from the packed identity R0."""
    R = R0
    d = NB.shape[1]
    for _ in range(D):
        new = R.copy()
        for l in range(d):
            new |= R[NB[:, l]]
        if np.array_equal(new, R):
            break
        R = new
    return n * n - int(_POP8[R].sum())


def _pick_pairs(work, A, d, rng):
    """Choose d-1 edges (a, b) with pairwise distinct a's and distinct b's, or None."""
    order = list(A)
    rng.shuffle(order)
    chosen = []
    usedB = set()
    for a in order:
        if len(chosen) == d - 1:
            break
        opts = [int(b) for b in work[a] if int(b) not in usedB]
        if not opts:
            continue
        b = rng.choice(opts)
        chosen.append((a, b))
        usedB.add(b)
    return chosen if len(chosen) == d - 1 else None


def _anneal(NB, n, A, D, d, rng, deadline):
    """2-switch annealing on the d-regular bipartite table NB (modified in place). True if diameter <= D."""
    R0 = np.packbits(np.eye(n, dtype=bool), axis=1)
    cost = _unreached_pairs(NB, n, D, R0)
    if cost == 0:
        return True
    c0 = float(cost)
    it = 0
    while time.monotonic() < deadline:
        if cost == 0:
            return True
        it += 1
        a1 = A[rng.randrange(len(A))]
        a2 = A[rng.randrange(len(A))]
        i1 = rng.randrange(d)
        i2 = rng.randrange(d)
        b1 = int(NB[a1, i1])
        b2 = int(NB[a2, i2])
        if (NB[a1] == b2).any() or (NB[a2] == b1).any():
            continue
        j1 = int(np.flatnonzero(NB[b1] == a1)[0])
        j2 = int(np.flatnonzero(NB[b2] == a2)[0])
        NB[a1, i1] = b2
        NB[a2, i2] = b1
        NB[b1, j1] = a2
        NB[b2, j2] = a1
        c2 = _unreached_pairs(NB, n, D, R0)
        temp = max(0.5, 0.01 * c0)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            NB[a1, i1] = b1
            NB[a2, i2] = b2
            NB[b1, j1] = a1
            NB[b2, j2] = a2
    return cost == 0


def _nb_edges(NB, n):
    """Edge list (u, v) with u < v from the neighbour table."""
    edges = []
    for u in range(n):
        for v in NB[u]:
            v = int(v)
            if u < v:
                edges.append((u, v))
    return edges


def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of the graph, or None if it is not bipartite."""
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


def _grow(d, D, n, edges, rng, deadline):
    """Repeated pair insertion followed by 2-switch annealing. Returns the largest valid (n, edges) found."""
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    if any(x != d for x in deg):
        return n, edges
    NB = np.zeros((n, d), dtype=np.int64)
    fill = [0] * n
    for u, v in edges:
        NB[u, fill[u]] = v
        fill[u] += 1
        NB[v, fill[v]] = u
        fill[v] += 1
    A = [v for v in range(n) if color[v] == 0]
    cur_n, cur_NB, cur_A, cur_edges = n, NB, A, list(edges)

    while time.monotonic() < deadline:
        N2 = cur_n + 2
        work = np.vstack([cur_NB, np.zeros((2, d), dtype=np.int64)])
        chosen = _pick_pairs(work, cur_A, d, rng)
        if chosen is None:
            continue
        x, y = cur_n, cur_n + 1
        for i, (a, b) in enumerate(chosen):
            ia = int(np.flatnonzero(work[a] == b)[0])
            work[a, ia] = y
            ib = int(np.flatnonzero(work[b] == a)[0])
            work[b, ib] = x
            work[x, i] = b
            work[y, i] = a
        work[x, d - 1] = y
        work[y, d - 1] = x
        A2 = cur_A + [x]
        att = min(deadline, time.monotonic() + 3.0)
        if _anneal(work, N2, A2, D, d, rng, att):
            e2 = _nb_edges(work, N2)
            if lib.is_valid(N2, e2, d, D):
                cur_n, cur_NB, cur_A, cur_edges = N2, work, A2, e2
    return cur_n, cur_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.5 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # NEW: insertion + 2-switch annealing to grow the best regular graph.
    if d >= 2 and D >= 2:
        try:
            n2, e2 = _grow(d, D, best_n, best[1], rng, deadline)
            if n2 > best_n:
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
