import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bound and safe baselines.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D <= 0 or d <= 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New engine: greedy bi-Cayley construction over semidirect products.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h (2kG vertices).
# A dart (i, j, s) joins A_i,g to B_j,mul(g,s) for all g. Each layer is a
# permutation p of range(k) with one dart (i, p[i], s_i) per i, so every
# vertex gets exactly one edge per layer and the degree is d after d layers.
# Distinct (i, j, s) triples guarantee there are no duplicate edges.
#
# The voltages are chosen greedily to minimise the number of (representative,
# vertex) pairs that are farther than D apart, evaluated with dense numpy
# reachability from the 2k representatives. Adding edges never increases a
# distance, so the partial cost is a monotone guide. A short plateau walk
# refines the result. If the lift still misses pairs, the far-off vertices
# are deleted, then spare degree is filled with opposite-side edges.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    for _ in range(40):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(N, reps, G, k, D, darts, M):
    """Number of (representative, vertex) pairs at distance > D in the partial lift."""
    ar = np.arange(G)
    rows = []
    cols = []
    for i, j, s in darts:
        rows.append(i * G + ar)
        cols.append((k + j) * G + M[:, s])
    R = np.concatenate(rows)
    C = np.concatenate(cols)
    A = np.zeros((N, N), dtype=np.float32)
    A[R, C] = 1.0
    A[C, R] = 1.0
    X = np.zeros((len(reps), N), dtype=np.float32)
    X[np.arange(len(reps)), reps] = 1.0
    for _ in range(D):
        X = np.minimum(X + X @ A, 1.0)
    return int(X.size - np.count_nonzero(X))


def _edges(N, k, G, darts, M):
    ar = np.arange(G)
    E = []
    for i, j, s in darts:
        E.extend(zip((i * G + ar).tolist(), ((k + j) * G + M[:, s]).tolist()))
    return E


def _repair(N, edges, D, rng, deadline):
    """Delete far-off vertices in batches until the diameter condition holds.

    Returns (orig_indices, new_edges) or (None, None).
    """
    E = np.asarray(edges, dtype=np.int64)
    alive = np.ones(N, dtype=bool)
    while True:
        if time.monotonic() > deadline:
            return None, None
        idx = np.nonzero(alive)[0]
        n = len(idx)
        if n == 0:
            return None, None
        pos = np.full(N, -1, dtype=np.int64)
        pos[idx] = np.arange(n)
        mask = alive[E[:, 0]] & alive[E[:, 1]]
        U = pos[E[mask, 0]]
        V = pos[E[mask, 1]]
        A = np.zeros((n, n), dtype=np.float32)
        A[U, V] = 1.0
        A[V, U] = 1.0
        X = np.eye(n, dtype=np.float32)
        for _ in range(D):
            X = np.minimum(X + X @ A, 1.0)
        bad = n - X.sum(axis=1)
        badv = np.nonzero(bad > 0.5)[0]
        if len(badv) == 0:
            return idx.tolist(), list(zip(U.tolist(), V.tolist()))
        order = sorted(badv.tolist(), key=lambda t: (-bad[t], rng.random()))
        for t in order[:max(1, len(badv) // 10)]:
            alive[idx[t]] = False


def _saturate(n, edges, color, d, rng):
    """Add cross-side edges between deficient vertices (never breaks the diameter)."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _trial(d, D, k, G, rng, deadline, cand_n=10, sweep_evals=1500):
    """One greedy-plus-sweep lift attempt. Returns (n, edges) or None."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    _, mul = g
    M = np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)
    N = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    used = set()
    darts = []

    # Greedy layer-by-layer construction.
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        order_i = list(range(k))
        rng.shuffle(order_i)
        for i in order_i:
            j = p[i]
            pool = [s for s in range(G) if (i, j, s) not in used]
            if not pool:
                return None
            cands = rng.sample(pool, min(cand_n, len(pool)))
            bc, bs = None, None
            for s in cands:
                if time.monotonic() > deadline:
                    return None
                c = _cost(N, reps, G, k, D, darts + [(i, j, s)], M)
                if bc is None or c < bc:
                    bc, bs = c, s
            darts.append((i, j, bs))
            used.add((i, j, bs))

    cur = _cost(N, reps, G, k, D, darts, M)

    # Plateau-tolerant voltage sweeps.
    ev = 0
    while cur > 0 and ev < sweep_evals and time.monotonic() < deadline:
        idx = rng.randrange(len(darts))
        i, j, s0 = darts[idx]
        used.discard((i, j, s0))
        pool = [s for s in range(G) if (i, j, s) not in used and s != s0]
        best_c, best_s = cur, s0
        for s in rng.sample(pool, min(6, len(pool))):
            darts[idx] = (i, j, s)
            c = _cost(N, reps, G, k, D, darts, M)
            ev += 1
            if c <= best_c:
                best_c, best_s = c, s
        darts[idx] = (i, j, best_s)
        used.add((i, j, best_s))
        cur = best_c

    edges = _edges(N, k, G, darts, M)
    if cur == 0:
        return N, edges

    # Near miss: delete far-off vertices, then fill the spare degree.
    orig, e = _repair(N, edges, D, rng, deadline)
    if orig is None:
        return None
    n = len(orig)
    color = [0 if o < k * G else 1 for o in orig]
    e = _saturate(n, e, color, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

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
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n >= _moore(d, D):
        return best

    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        lo = best_n // (2 * k) + 1
        lo = max(lo, 2)
        G = rng.randint(lo, lo + max(2, lo // 16))
        res = _trial(d, D, k, G, rng, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
