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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2, with an optional
# "partial lift + matching completion" mode.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so with dl layers every vertex has degree dl.
#
# NEW: matching completion. A structured lift with dl = d-1 layers is searched
# (it is a (d-1)-regular bipartite graph, which is easier to fit to diameter D),
# then the last degree is supplied by a random perfect matching between the A
# side and the B side, avoiding existing edges. Adding edges never increases
# distances, so the completed graph is still regular of degree d, and the
# best of several random matchings (ranked by lib.bad_pairs) is kept if valid.
#
# Moves in the lift search:
#   * voltage move (random block),
#   * layer-swap move (exchange B-targets of two A-blocks in one layer),
#   * defect-targeted voltage move aimed at vertices still missing reach.
# A bandit over base sizes k decides how much budget each k receives.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_FILL_P = 0.5
_MATCH_TRIALS = 12


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type: (a,b)(c,e) = (a + (-1)^b c, b+e)
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, built with one numpy broadcast.
    """
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
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr):
    """Bitmask per vertex: bit b is set when representative block b is within distance D.

    Left multiplication is an automorphism, so the 2k block starts cover all orbits.
    nbr has one row per layer, so the number of layers is nbr.shape[0].
    """
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for row in nbr:
            new |= reach[row]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(dl, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over dl-layer lifts.

    Returns (best_cost, N, edge_set) where edge_set comes from the best state seen.
    best_cost == 0 means the structured lift itself is valid.
    """
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(dl)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(dl)]
    nbr = np.empty((dl, N), dtype=np.int64)
    for l in range(dl):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(dl) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    best_nbr = nbr.copy()

    for t in range(iters):
        if cost < best_cost:
            best_cost = cost
            best_nbr = nbr.copy()
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            # Layer-swap move: exchange the B-targets of two A-blocks in one layer.
            l = rng.randrange(dl)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        # Voltage move: defect-targeted with probability 0.4, otherwise uniform.
        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(dl)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(dl)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost < best_cost:
        best_cost = cost
        best_nbr = nbr.copy()

    edges = set()
    for u in range(k * G):
        for v in best_nbr[:, u]:
            edges.add((u, int(v)))
    return best_cost, N, edges


# ----------------------------------------------------------------------------
# NEW helper: random perfect matching completion.
# ----------------------------------------------------------------------------

def _random_matching(A, N, forb, rng):
    """Random perfect matching between A-side [0, A) and B-side [A, N) avoiding the pairs in forb.

    Returns a list of (a, b) pairs, or None if repairing conflicts did not converge.
    """
    perm = list(range(A, N))
    rng.shuffle(perm)
    for _ in range(4000):
        conflicts = [a for a in range(A) if (a, perm[a]) in forb]
        if not conflicts:
            return [(a, perm[a]) for a in range(A)]
        a = rng.choice(conflicts)
        j = rng.randrange(A)
        perm[a], perm[j] = perm[j], perm[a]
    return None


def _matching_fill(N, A, forb, d, D, rng, trials):
    """Complete a (d-1)-regular bipartite graph to a d-regular one by random perfect matchings.

    Returns (N, sorted_edges) if some matching gives a valid graph, else None.
    """
    deg = [0] * N
    for a, b in forb:
        deg[a] += 1
        deg[b] += 1
    if any(x != d - 1 for x in deg):
        return None
    best_edges, best_bad = None, None
    for _ in range(trials):
        M = _random_matching(A, N, forb, rng)
        if M is None:
            continue
        edges = list(forb) + M
        bad = lib.bad_pairs(N, edges, D)
        if best_bad is None or bad < best_bad:
            best_edges, best_bad = edges, bad
        if bad == 0:
            break
    if best_edges is not None and best_bad == 0 and lib.is_valid(N, best_edges, d, D):
        return N, sorted(best_edges)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Use nearly the whole limit: the final validity check is cheap at these sizes.
    budget = max(1.0, min(0.92 * time_limit, time_limit - 4.0))
    deadline = start + budget
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

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search with the bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
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

        use_fill = d >= 3 and rng.random() < _FILL_P
        dl = d - 1 if use_fill else d
        cost, N, sedges = _search(dl, D, k, G, Ts, Invs, rng, deadline, 4000)
        if not use_fill:
            if cost == 0:
                wins[k] += 1
                consider(N, sorted(sedges))
        else:
            res = _matching_fill(N, k * G, sedges, d, D, rng, _MATCH_TRIALS)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
