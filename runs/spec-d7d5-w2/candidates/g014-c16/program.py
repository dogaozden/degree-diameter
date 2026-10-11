import math
import random
import time

import numpy as np

import lib


_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _circulant(N, d):
    """d-regular bipartite graph on N + N vertices: A_i ~ B_{i+s}, s = 0..d-1. Needs N >= d."""
    nbr = np.zeros((2 * N, d), dtype=np.int64)
    for i in range(N):
        for s in range(d):
            j = (i + s) % N
            nbr[i, s] = N + j
            nbr[N + j, s] = i
    color = np.array([0] * N + [1] * N, dtype=np.int64)
    return nbr, color


def _reach_bits(n, nbr, D):
    """Bitset reach: row v has bit u set when dist(v, u) <= D."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        acc = np.bitwise_or.reduce(reach[nbr], axis=1)
        new = reach | acc
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _bad(n, nbr, D):
    """Ordered count of pairs at distance > D (0 iff diameter <= D and connected)."""
    reach = _reach_bits(n, nbr, D)
    tot = int(_POP8[reach.view(np.uint8)].sum())
    return n * n - tot


def _anneal(nbr, color, D, rng, deadline, max_iter, T0):
    """Simulated annealing over 2-switches (keeps d-regularity and bipartiteness).

    Modifies nbr in place. Returns True iff the final graph has cost 0.
    """
    n, d = nbr.shape
    A = np.flatnonzero(color == 0)
    cost = _bad(n, nbr, D)
    it = 0
    while cost > 0 and it < max_iter:
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        it += 1
        T = T0 * (1.0 - it / max_iter) + 0.05
        a1 = int(A[rng.randrange(len(A))])
        a2 = int(A[rng.randrange(len(A))])
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        b1 = int(nbr[a1, i])
        b2 = int(nbr[a2, j])
        if b1 == b2 or (nbr[a2] == b1).any() or (nbr[a1] == b2).any():
            continue
        p = int(np.flatnonzero(nbr[b1] == a1)[0])
        q = int(np.flatnonzero(nbr[b2] == a2)[0])
        nbr[a1, i] = b2
        nbr[a2, j] = b1
        nbr[b1, p] = a2
        nbr[b2, q] = a1
        new = _bad(n, nbr, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            nbr[b1, p] = a1
            nbr[b2, q] = a2
            nbr[a1, i] = b1
            nbr[a2, j] = b2
    return cost == 0


def _insert_pairs(nbr, color, d, rng, count):
    """Insert `count` vertex pairs by the pair-insertion step. Returns (nbr, color) copies or None.

    Remove d-1 edges (a_i, b_i) with distinct a's and distinct b's; add x (side 0) ~ b_i,
    y (side 1) ~ a_i, and x ~ y. All degrees stay d; the result is a new graph that may
    have diameter defects, which the annealer then repairs.
    """
    nbr = nbr.copy()
    color = color.copy()
    for _ in range(count):
        n = nbr.shape[0]
        A = np.flatnonzero(color == 0)
        chosen = []
        used_a, used_b = set(), set()
        tries = 0
        while len(chosen) < d - 1 and tries < 50 * d:
            tries += 1
            a = int(A[rng.randrange(len(A))])
            b = int(nbr[a, rng.randrange(d)])
            if a in used_a or b in used_b:
                continue
            chosen.append((a, b))
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            return None
        x, y = n, n + 1
        nbr = np.vstack([nbr, np.zeros((2, d), dtype=np.int64)])
        color = np.concatenate([color, np.array([0, 1], dtype=np.int64)])
        for a, b in chosen:
            pa = int(np.flatnonzero(nbr[a] == b)[0])
            nbr[a, pa] = y
            pb = int(np.flatnonzero(nbr[b] == a)[0])
            nbr[b, pb] = x
        nbr[x, :d - 1] = [b for _, b in chosen]
        nbr[x, d - 1] = y
        nbr[y, :d - 1] = [a for a, _ in chosen]
        nbr[y, d - 1] = x
    return nbr, color


def _edges_from(nbr, color):
    """Edge list from the adjacency array, each edge listed once from its side-0 end."""
    n = nbr.shape[0]
    edges = []
    for a in np.flatnonzero(color == 0):
        a = int(a)
        for b in nbr[a]:
            edges.append((a, int(b)))
    return n, edges


def _grow(d, D, rng, deadline):
    """Anneal a circulant start, then repeatedly insert pairs and re-anneal. Returns (n, edges) or None."""
    N = max(d, 40)
    nbr, color = _circulant(N, d)
    if not _anneal(nbr, color, D, rng, deadline, 4000, 3.0):
        return None
    best_nbr, best_color = nbr, color
    step = max(1, N // 20)
    fails = 0
    while time.monotonic() < deadline and fails < 60:
        out = _insert_pairs(best_nbr, best_color, d, rng, step)
        if out is None:
            fails += 1
            continue
        cn, cc = out
        if _anneal(cn, cc, D, rng, deadline, 800, 2.0):
            best_nbr, best_color = cn, cc
            N = best_nbr.shape[0] // 2
            fails = 0
            step = min(step * 2, max(1, N // 10))
        else:
            fails += 1
            step = max(1, step // 2)
    return _edges_from(best_nbr, best_color)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        try:
            res = _grow(d, D, rng, deadline)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
