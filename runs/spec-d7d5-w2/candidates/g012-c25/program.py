import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent as safe baselines).
# ----------------------------------------------------------------------------

_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: random-regular bipartite graphs repaired by 2-switch
# annealing, grown vertex-pair by vertex-pair.
#
# State = (nbr, isA, A, B):
#   nbr[v, :] are the d neighbours of v (always simple and d-regular, bipartite),
#   isA[v] is True for the A side, A / B are the vertex lists of each side.
# Cost = number of unordered vertex pairs at distance > D (bitset BFS in numpy).
# Moves: 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which preserve regularity
# and bipartiteness. Targeted moves aim at a currently unreached pair.
# Growth inserts two vertices x (side A), y (side B) with x~y, removing d-1
# disjoint edges, which keeps every degree at d.
# ----------------------------------------------------------------------------

def _reach(nbr, n, D):
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n, dtype=np.int64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    d = nbr.shape[1]
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[:, l]]
        reach = new
    return reach


def _cost(nbr, D):
    n = nbr.shape[0]
    reach = _reach(nbr, n, D)
    total = int(_POP16[reach.view(np.uint16)].sum())
    return (n * n - total) // 2, reach


def _switch(nbr, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Returns an undo record or None."""
    if a1 == a2 or b1 == b2:
        return None
    if (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
        return None
    c1 = int(np.flatnonzero(nbr[a1] == b1)[0])
    c2 = int(np.flatnonzero(nbr[a2] == b2)[0])
    s1 = int(np.flatnonzero(nbr[b1] == a1)[0])
    s2 = int(np.flatnonzero(nbr[b2] == a2)[0])
    nbr[a1, c1] = b2
    nbr[a2, c2] = b1
    nbr[b1, s1] = a2
    nbr[b2, s2] = a1
    return (a1, c1, b1, s1, a2, c2, b2, s2)


def _revert(nbr, mv):
    a1, c1, b1, s1, a2, c2, b2, s2 = mv
    nbr[a1, c1] = b1
    nbr[b1, s1] = a1
    nbr[a2, c2] = b2
    nbr[b2, s2] = a2


def _targeted(nbr, isA, reach, n, d, rng):
    u = rng.randrange(n)
    bits = np.unpackbits(reach[u].view(np.uint8), bitorder="little")[:n]
    missing = np.flatnonzero(bits == 0)
    if missing.size == 0:
        return None
    v = int(missing[rng.randrange(missing.size)])
    if bool(isA[v]) == bool(isA[u]):
        b2 = int(nbr[v, rng.randrange(d)])          # opposite side of u, adjacent to v
    else:
        w = int(nbr[v, rng.randrange(d)])           # same side as u
        b2 = int(nbr[w, rng.randrange(d)])          # opposite side of u, distance 2 from v
    a2 = int(nbr[b2, rng.randrange(d)])             # same side as u
    b1 = int(nbr[u, rng.randrange(d)])
    return _switch(nbr, u, b1, a2, b2)


def _random_move(nbr, isA, A, B, n, d, rng):
    u = rng.randrange(n)
    lst = A if bool(isA[u]) else B
    a2 = lst[rng.randrange(len(lst))]
    b1 = int(nbr[u, rng.randrange(d)])
    b2 = int(nbr[a2, rng.randrange(d)])
    return _switch(nbr, u, b1, a2, b2)


def _anneal(state, d, D, rng, deadline, T0):
    nbr, isA, A, B = state
    n = nbr.shape[0]
    cost, reach = _cost(nbr, D)
    if cost == 0:
        return state, True
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.05, T0 * (1.0 - (now - t0) / span))
        if rng.random() < 0.5:
            mv = _targeted(nbr, isA, reach, n, d, rng)
        else:
            mv = _random_move(nbr, isA, A, B, n, d, rng)
        if mv is None:
            continue
        c2, r2 = _cost(nbr, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost, reach = c2, r2
        else:
            _revert(nbr, mv)
    return state, cost == 0


def _grow(state, d, pairs, rng):
    """Insert `pairs` new (x in A, y in B) pairs, keeping d-regularity and bipartiteness."""
    nbr, isA, A, B = state
    nbr = nbr.copy()
    isA = isA.copy()
    A = list(A)
    B = list(B)
    for _ in range(pairs):
        order = A[:]
        rng.shuffle(order)
        chosen = []
        usedb = set()
        for a in order:
            if len(chosen) == d - 1:
                break
            c = rng.randrange(d)
            b = int(nbr[a, c])
            if b in usedb:
                continue
            usedb.add(b)
            chosen.append((a, c, b))
        if len(chosen) < d - 1:
            return None
        n = nbr.shape[0]
        x, y = n, n + 1
        xs, ys = [], []
        for a, c, b in chosen:
            nbr[a, c] = y                       # a loses b, gains y
            s = int(np.flatnonzero(nbr[b] == a)[0])
            nbr[b, s] = x                       # b loses a, gains x
            xs.append(b)
            ys.append(a)
        xs.append(y)
        ys.append(x)
        nbr = np.vstack([nbr, np.array([xs, ys], dtype=np.int64)])
        isA = np.concatenate([isA, np.array([True, False])])
        A.append(x)
        B.append(y)
    return nbr, isA, A, B


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D, order 2D (Moore bound).
        n2 = 2 * D
        return n2, [(i, (i + 1) % n2) for i in range(n2)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = list(lib.haar_graph(d, range(d)))
    if D == 2:
        return best[0], best[1]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = [pg[0], pg[1]]
            if D == 3 and lib.is_prime_power(d - 1):
                return best[0], best[1]

    if D == 4 and time.monotonic() < start + 0.2 * budget:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = [gq[0], gq[1]]
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best[0], best[1]

    # Annealing growth from K_{d,d}.
    nbr0 = np.empty((2 * d, d), dtype=np.int64)
    nbr0[:d] = np.arange(d, 2 * d)[None, :]
    nbr0[d:] = np.arange(d)[None, :]
    isA0 = np.array([True] * d + [False] * d)
    cur = (nbr0, isA0, list(range(d)), list(range(d, 2 * d)))
    successes = [cur]
    step = 4
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0.2:
            break
        cap = max(0.5, 0.35 * remaining)
        cand = _grow(cur, d, step, rng)
        if cand is None:
            if step == 1:
                break
            step = max(1, step // 2)
            continue
        cand, ok = _anneal(cand, d, D, rng,
                           min(deadline, time.monotonic() + cap), 0.8)
        if ok:
            cur = cand
            successes.append(cur)
            step = min(2 * step, 64)
        else:
            if step == 1:
                break
            step //= 2

    # Take the largest successful state that passes the exact validity check.
    for st in reversed(successes):
        nbr, isA, A, B = st
        n = nbr.shape[0]
        if n <= best[0]:
            break
        edges = [(int(a), int(b)) for a in A for b in nbr[a].tolist()]
        if lib.is_valid(n, edges, d, D):
            best = [n, edges]
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = list(lib.haar_graph(d, range(d)))
    return best[0], best[1]
