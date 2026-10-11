import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact small family: PG(2, q) incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold new family: random d-regular bipartite graphs on 2h vertices, found by
# simulated annealing over degree-preserving double-edge switches, minimizing
# the number of vertex pairs at distance > D. No group structure is imposed.
# ----------------------------------------------------------------------------

def _bad_pairs(nbr, n, D):
    """Number of unordered vertex pairs at distance > D (bitset reachability in numpy)."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[1]):
            new |= reach[nbr[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    cnt = int(_POP16[reach.view(np.uint16)].sum())
    return (n * n - cnt) // 2


def _switch(nbr, a1, l1, a2, l2):
    """Double-edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Applying it again with the same
    indices undoes it."""
    b1 = int(nbr[a1, l1])
    b2 = int(nbr[a2, l2])
    nbr[a1, l1] = b2
    nbr[a2, l2] = b1
    r = int(np.flatnonzero(nbr[b1] == a1)[0])
    nbr[b1, r] = a2
    s = int(np.flatnonzero(nbr[b2] == a2)[0])
    nbr[b2, s] = a1


def _try_switch(nbr, a1, l1, a2, l2):
    """Apply a switch if it keeps the graph simple. Returns True if applied."""
    b1 = int(nbr[a1, l1])
    b2 = int(nbr[a2, l2])
    if b1 == b2 or (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
        return False
    _switch(nbr, a1, l1, a2, l2)
    return True


def _regular_anneal(h, d, D, rng, deadline, iters):
    """Anneal a random d-regular bipartite graph on sides of size h. Returns nbr or None.

    A-vertices are 0..h-1, B-vertices are h..2h-1. nbr[v, l] is the l-th neighbour of v.
    """
    n = 2 * h
    nbr = np.empty((n, d), dtype=np.int64)
    ii = np.arange(h)
    for l in range(d):
        nbr[:h, l] = h + (ii + l) % h   # Haar start, distinct shifts (needs h >= d)
        nbr[h:, l] = (ii - l) % h
    # Randomize towards a random regular graph.
    for _ in range(8 * n):
        a1 = rng.randrange(h)
        a2 = rng.randrange(h)
        if a1 == a2:
            continue
        _try_switch(nbr, a1, rng.randrange(d), a2, rng.randrange(d))
    cost = _bad_pairs(nbr, n, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        a1 = rng.randrange(h)
        a2 = rng.randrange(h)
        if a1 == a2:
            continue
        l1 = rng.randrange(d)
        l2 = rng.randrange(d)
        if not _try_switch(nbr, a1, l1, a2, l2):
            continue
        c2 = _bad_pairs(nbr, n, D)
        temp = max(0.3, 1.5 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            _switch(nbr, a1, l1, a2, l2)  # undo
    return nbr if cost == 0 else None


def _phase_regular(state, d, D, rng, deadline, consider, best_n):
    """Search for valid random regular bipartite graphs with growing h."""
    while time.monotonic() < deadline:
        state["h"] = max(state["h"], best_n() // 2)
        h = state["h"] + state["step"]
        chunk_end = min(deadline, time.monotonic() + state["chunk"])
        nbr = _regular_anneal(h, d, D, rng, chunk_end, 3000)
        if nbr is not None:
            edges = [(a, int(nbr[a, l])) for a in range(h) for l in range(d)]
            if consider(2 * h, edges):
                state["h"] = h
                state["step"] = min(state["step"] * 2, 64)
                continue
        state["step"] = max(1, state["step"] // 2)


# ----------------------------------------------------------------------------
# Parent family: bi-Cayley lifts over semidirect products Z_m x| Z_k2, kept as
# a second search phase so the program does not depend on one method alone.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP16 = _POP
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 with element a*k2+b and (a,b)(c,e) = (a+r^b c, b+e)."""
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


def _phase_bicayley(d, D, rng, deadline, consider, best_n):
    """Bandit over base sizes k for bi-Cayley lift searches."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n() // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n():
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Driver. Schedule: regular-graph annealing (60% of budget), bi-Cayley search
# (to 80%), then regular-graph annealing for the rest. Every candidate passes
# lib.is_valid before it replaces the incumbent, and K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    end = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    holder = {"best": lib.haar_graph(d, range(d))}  # K_{d,d}: valid for D >= 2

    def best_n():
        return holder["best"][0]

    def consider(n, e):
        if n > holder["best"][0] and lib.is_valid(n, e, d, D):
            holder["best"] = (n, e)
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return holder["best"]

    state = {"h": max(d, best_n() // 2), "step": max(1, d), "chunk": max(3.0, 0.15 * budget)}

    tA = min(end, start + 0.6 * budget)
    tB = min(end, start + 0.8 * budget)
    _phase_regular(state, d, D, rng, tA, consider, best_n)
    if time.monotonic() < tB:
        _phase_bicayley(d, D, rng, tB, consider, best_n)
    if time.monotonic() < end:
        _phase_regular(state, d, D, rng, end, consider, best_n)

    n, e = holder["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
