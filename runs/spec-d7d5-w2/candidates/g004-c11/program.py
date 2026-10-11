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


def _araujo(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
#
# New in this version: "iterated local search with cross-layer exchange".
#   * Cross-layer exchange move: swap the voltages of the same base vertex i
#     between two layers l1 != l2. It keeps every layer a permutation and
#     reshuffles the voltage multiset of each base vertex, a move the older
#     search could not make.
#   * Iterated local search: when an annealing run ends with cost > 0, the best
#     state is perturbed by a few random moves and annealed again from there,
#     instead of always restarting from a fresh random or structured state.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.25
_XCH_PROB = 0.25
_STRUCT_PROB = 0.5
_ITERS = 4000
_ILS_ROUNDS = 6
_ILS_KICKS = 3
_ILS_THRESH = 60  # only perturb states whose best cost is at most this


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
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

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = M[g, s] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start: layers[l][i] = (i + l) mod k, S[l][i] = y_i * x^(l+1)."""
    x = rng.randrange(1, G)
    powers = [0]  # identity element is index 0
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    """Uniform start: random permutation per layer and random voltages."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-vertex i and B-vertex j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _build_nbr(d, k, G, Ts, Invs, layers, S):
    """Full neighbour table: nbr[l, v] is the layer-l neighbour of vertex v."""
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
    return nbr


def _dup(d, k, layers, S):
    """Number of repeated (base A, base B, voltage) triples, which would be duplicate edges."""
    keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
    return len(keys) - len(set(keys))


def _cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs over all 2k representatives.

    Bit b of reach[v] is set when representative block b is within distance t of v.
    Left multiplication is an automorphism, so the 2k block starts cover all orbits.
    """
    d, N = nbr.shape
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
    return 2 * k * N - int(_POP[reach].sum())


def _full_cost(d, k, G, D, Ts, Invs, layers, S):
    nbr = _build_nbr(d, k, G, Ts, Invs, layers, S)
    return _cost(k, G, D, nbr) + _PENALTY * _dup(d, k, layers, S)


def _anneal(d, D, k, G, Ts, Invs, rng, deadline, iters, layers, S):
    """Simulated annealing over voltages, target swaps and cross-layer exchanges.

    Returns (best_cost, best_layers, best_S) seen during the run.
    """
    cost = _full_cost(d, k, G, D, Ts, Invs, layers, S)
    best = (cost, [r[:] for r in layers], [r[:] for r in S])
    c0 = float(max(cost, 1))

    for t in range(iters):
        if best[0] == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        nl = [r[:] for r in layers]
        nS = [r[:] for r in S]
        mv = rng.random()
        if k > 1 and mv < _SWAP_PROB:
            # Swap the B-side targets of two base vertices in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            nl[l][i1], nl[l][i2] = nl[l][i2], nl[l][i1]
        elif d > 1 and mv < _SWAP_PROB + _XCH_PROB:
            # Cross-layer exchange: swap voltages of base vertex i between two layers.
            l1, l2 = rng.sample(range(d), 2)
            i = rng.randrange(k)
            nS[l1][i], nS[l2][i] = nS[l2][i], nS[l1][i]
        else:
            # Voltage change.
            l = rng.randrange(d)
            i = rng.randrange(k)
            v = rng.randrange(G)
            if v == nS[l][i]:
                continue
            nS[l][i] = v

        c2 = _full_cost(d, k, G, D, Ts, Invs, nl, nS)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            layers, S, cost = nl, nS, c2
            if cost < best[0]:
                best = (cost, [r[:] for r in layers], [r[:] for r in S])

    return best


def _perturb(d, k, G, rng, layers, S, kicks):
    """Copy a state and apply a few random voltage changes (iterated-local-search kick)."""
    nl = [r[:] for r in layers]
    nS = [r[:] for r in S]
    for _ in range(kicks):
        l = rng.randrange(d)
        i = rng.randrange(k)
        nS[l][i] = rng.randrange(G)
    return nl, nS


def _graph_from(d, k, G, Ts, Invs, layers, S):
    """Edge list of the lift described by (layers, S)."""
    N = 2 * k * G
    nbr = _build_nbr(d, k, G, Ts, Invs, layers, S)
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.92 * time_limit, time_limit - 4.0))
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

    if D == 3:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bandit over base sizes k, iterated local search per group.
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

        # Initial annealing run from a structured or random state.
        if rng.random() < _STRUCT_PROB:
            layers, S = _structured_init(d, k, G, Ts, rng)
        else:
            layers, S = _random_init(d, k, G, rng)
        cost, bl, bS = _anneal(d, D, k, G, Ts, Invs, rng, deadline, _ITERS, layers, S)

        # Iterated local search from the best state if it is close to valid.
        rounds = 0
        while cost > 0 and cost <= _ILS_THRESH and rounds < _ILS_ROUNDS \
                and time.monotonic() < deadline:
            rounds += 1
            pl, pS = _perturb(d, k, G, rng, bl, bS, _ILS_KICKS)
            c2, l2, S2 = _anneal(d, D, k, G, Ts, Invs, rng, deadline, _ITERS // 2, pl, pS)
            if c2 < cost:
                cost, bl, bS = c2, l2, S2

        if cost == 0:
            wins[k] += 1
            n, e = _graph_from(d, k, G, Ts, Invs, bl, bS)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
