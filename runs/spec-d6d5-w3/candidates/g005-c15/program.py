import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline constructions (valid for their D range, used as fallbacks).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) with the largest prime power q such that q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: fixed-order, d-regular bipartite graphs improved by edge-swap
# annealing on the number of pairs at distance > D. Orders grow by "vertex
# splitting", which keeps the graph d-regular and bipartite.
#
# Representation: nb is an int64 array of shape (2N, d). Rows 0..N-1 are the
# A side, rows N..2N-1 the B side; entries are combined indices.
# ----------------------------------------------------------------------------

_POP = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _from_pairs(N, pairs, d):
    """Build the combined neighbour array from (A index, B index) pairs."""
    Aadj = [[] for _ in range(N)]
    Badj = [[] for _ in range(N)]
    for x, y in pairs:
        Aadj[x].append(y)
        Badj[y].append(x)
    out = np.zeros((2 * N, d), dtype=np.int64)
    for a in range(N):
        out[a] = [N + b for b in Aadj[a]]
    for b in range(N):
        out[N + b] = Badj[b]
    return out


def _to_pairs(nb, N):
    """Return (A index, B index) pairs of a combined neighbour array."""
    return [(a, int(b) - N) for a in range(N) for b in nb[a].tolist()]


def _bad_pairs(nb, D):
    """Number of unordered vertex pairs at distance > D (bitset ball computation in numpy)."""
    M, d = nb.shape
    W = (M + 63) // 64
    reach = np.zeros((M, W), dtype=np.uint64)
    idx = np.arange(M, dtype=np.int64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for k in range(d):
            new |= reach[nb[:, k]]
        reach = new
    total = int(_POP[reach.view(np.uint8)].sum())
    return (M * M - total) // 2


def _swap(nb, x1, y1, x2, y2):
    """Replace edges x1-y1, x2-y2 by x1-y2, x2-y1 (A-side x, B-side y, combined indices)."""
    r = nb[x1]
    r[r == y1] = y2
    r = nb[x2]
    r[r == y2] = y1
    r = nb[y1]
    r[r == x1] = x2
    r = nb[y2]
    r[r == x2] = x1


def _anneal(nb, D, rng, deadline, iters, T0=3.0, T1=0.2):
    """Metropolis search over degree-preserving bipartite edge swaps. Modifies nb in place."""
    d = nb.shape[1]
    N = nb.shape[0] // 2
    cur = _bad_pairs(nb, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        a1 = rng.randrange(N)
        b1 = int(nb[a1, rng.randrange(d)])
        a2 = rng.randrange(N)
        b2 = int(nb[a2, rng.randrange(d)])
        if a1 == a2 or b1 == b2:
            continue
        if (nb[a1] == b2).any() or (nb[a2] == b1).any():
            continue
        _swap(nb, a1, b1, a2, b2)
        new = _bad_pairs(nb, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _swap(nb, a1, b2, a2, b1)
    return cur


def _split(nb, N, d, rng):
    """Add one vertex per side, keeping d-regularity and bipartiteness.

    Remove a random matching of d-1 edges (x_i, y_i); add a new A vertex joined to
    all y_i, a new B vertex joined to all x_i, and the edge between the two new vertices.
    Returns (nb, N+1) or None if no matching of size d-1 was found.
    """
    pairs = _to_pairs(nb, N)
    rng.shuffle(pairs)
    usedA, usedB, chosen = set(), set(), []
    for x, y in pairs:
        if x in usedA or y in usedB:
            continue
        chosen.append((x, y))
        usedA.add(x)
        usedB.add(y)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    chosen_set = set(chosen)
    newpairs = [p for p in pairs if p not in chosen_set]
    NA = N
    NB = N
    for x, y in chosen:
        newpairs.append((NA, y))
        newpairs.append((x, NB))
    newpairs.append((NA, NB))
    N2 = N + 1
    out = _from_pairs(N2, newpairs, d)
    return out, N2


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if best[0] == moore:
                return best
    except Exception:
        pass
    try:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    except Exception:
        pass

    # Main search: grow a d-regular bipartite graph by vertex splitting, repairing
    # each grown graph to diameter <= D by edge-swap annealing. Every accepted
    # graph is verified with lib.is_valid.
    try:
        N_good = d
        good = _from_pairs(d, [(a, b) for a in range(d) for b in range(d)], d)
        iters = 5000
        step = max(1, d // 4)
        while time.monotonic() < deadline:
            cand, Nc = good.copy(), N_good
            ok = True
            for _ in range(step):
                res = _split(cand, Nc, d, rng)
                if res is None:
                    ok = False
                    break
                cand, Nc = res
            if not ok:
                step = max(1, step // 2)
                continue

            cost = _bad_pairs(cand, D)
            if cost > 0:
                cost = _anneal(cand, D, rng, deadline, iters)

            if cost == 0:
                edges = [(a, Nc + b) for a, b in _to_pairs(cand, Nc)]
                if lib.is_valid(2 * Nc, edges, d, D):
                    good, N_good = cand, Nc
                    if 2 * Nc > best[0]:
                        best = (2 * Nc, edges)
                    step = min(step * 2, max(1, N_good // 8))
                else:
                    step = max(1, step // 2)
            else:
                if step == 1:
                    iters = min(iters * 2, 60000)
                step = max(1, step // 2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
