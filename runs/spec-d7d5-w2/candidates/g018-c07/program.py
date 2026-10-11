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
    """Bitmask per vertex over the 2k block representatives (left multiplication is an automorphism)."""
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
# NEW: degree-preserving vertex-pair insertion with 2-switch repair.
#
# A d-regular bipartite graph H is grown by two vertices at a time:
#   pick d pairwise-disjoint edges (a_i, b_i); delete them; add a* adjacent to
#   all b_i and b* adjacent to all a_i. Every degree stays exactly d, bipartiteness
#   is kept, and the order rises by 2. The new diameter defects are then removed
#   by annealing over 2-switches (a1 b1, a2 b2) -> (a1 b2, a2 b1), which also keep
#   the graph d-regular and bipartite.
# ----------------------------------------------------------------------------

def _adj_slots(n, edges, d):
    """Return (nbr, isA) with nbr[v, s] the s-th neighbour of v, or None if not d-regular bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return None
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
    nbr = np.array(adj, dtype=np.int64)
    isA = np.array([c == 0 for c in color], dtype=bool)
    return nbr, isA


def _slots_edges(nbr, isA):
    """Edge list (a, b) from the slot representation (each edge listed once, from its A end)."""
    out = []
    for a in np.flatnonzero(isA).tolist():
        for b in nbr[a].tolist():
            out.append((a, b))
    return out


def _bitreach(nbr, D):
    """Packed bitsets: bit v of reach[u] is set when dist(u, v) <= D."""
    N, d = nbr.shape
    W = (N + 63) // 64
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached_bits(reach, N):
    """Number of ordered vertex pairs at distance > D."""
    pops = int(_POP8[reach.view(np.uint8)].sum())
    return N * N - pops


def _swap(nbr, a1, s1, a2, s2):
    """Degree-preserving 2-switch. Self-inverse when called again with the same arguments."""
    b1 = int(nbr[a1, s1])
    b2 = int(nbr[a2, s2])
    t1 = int(np.flatnonzero(nbr[b1] == a1)[0])
    t2 = int(np.flatnonzero(nbr[b2] == a2)[0])
    nbr[a1, s1] = b2
    nbr[a2, s2] = b1
    nbr[b1, t1] = a2
    nbr[b2, t2] = a1


def _insert_pair(nbr, isA, d, rng):
    """Add one A vertex and one B vertex by rewiring a disjoint matching of d edges. Returns (nbr, isA) or None."""
    N = nbr.shape[0]
    A = np.flatnonzero(isA).tolist()
    if len(A) < d:
        return None
    As, Bs = None, None
    for _ in range(200):
        cand = rng.sample(A, d)
        slots = [rng.randrange(d) for _ in range(d)]
        bs = [int(nbr[a, s]) for a, s in zip(cand, slots)]
        if len(set(bs)) == d:
            As, Bs = cand, bs
            break
    if As is None:
        return None
    new_a, new_b = N, N + 1
    nb = np.empty((N + 2, d), dtype=np.int64)
    nb[:N] = nbr
    nb[new_a] = Bs
    nb[new_b] = As
    for a, b in zip(As, Bs):
        s = int(np.flatnonzero(nb[a] == b)[0])
        nb[a, s] = new_b
        t = int(np.flatnonzero(nb[b] == a)[0])
        nb[b, t] = new_a
    ia = np.concatenate([isA, np.array([True, False])])
    return nb, ia


def _anneal_repair(nbr, isA, d, D, rng, deadline, iters):
    """Anneal over 2-switches until every pair is within distance D. Returns nbr or None."""
    nbr = nbr.copy()
    N = nbr.shape[0]
    A = np.flatnonzero(isA).tolist()
    cost = _unreached_bits(_bitreach(nbr, D), N)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        a1 = A[rng.randrange(len(A))]
        a2 = A[rng.randrange(len(A))]
        if a1 == a2:
            continue
        s1 = rng.randrange(d)
        s2 = rng.randrange(d)
        b1 = int(nbr[a1, s1])
        b2 = int(nbr[a2, s2])
        if b1 == b2 or np.any(nbr[a1] == b2) or np.any(nbr[a2] == b1):
            continue
        _swap(nbr, a1, s1, a2, s2)
        c2 = _unreached_bits(_bitreach(nbr, D), N)
        temp = 0.3 + 3.0 * (1.0 - t / iters)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            _swap(nbr, a1, s1, a2, s2)
    return nbr if cost == 0 else None


def _grow(nbr, isA, d, D, rng, deadline, consider):
    """Repeatedly insert a pair and repair; every success is offered to consider(n, edges)."""
    cur_nbr, cur_isA = nbr, isA
    while time.monotonic() < deadline:
        res = _insert_pair(cur_nbr, cur_isA, d, rng)
        if res is None:
            break
        nb, ia = res
        fixed = _anneal_repair(nb, ia, d, D, rng, deadline, 2000)
        if fixed is not None:
            cur_nbr, cur_isA = fixed, ia
            consider(fixed.shape[0], _slots_edges(fixed, ia))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 4.0))
    deadline = start + budget
    search_deadline = start + 0.5 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately (calibration-style cases).
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

    # Phase 1: bi-Cayley lift search with a bandit over base sizes k.
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

    # Phase 2 (new): grow the best regular graph by degree-preserving pair insertion.
    if time.monotonic() < deadline:
        slots = _adj_slots(best[0], best[1], d)
        if slots is not None:
            nbr0, isA0 = slots
            _grow(nbr0, isA0, d, D, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
