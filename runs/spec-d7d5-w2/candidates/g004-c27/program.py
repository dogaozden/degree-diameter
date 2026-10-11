import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions).
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
# Every layer is a permutation, so every vertex gets degree d.
#
# New in this version: ELITE ITERATED LOCAL SEARCH.
#   * Every failed annealing run leaves a best-so-far state for its group.
#   * Elite states are kept per group (k, m, k2, r), capped in size.
#   * Half the time, a new run warm-starts from an elite state after an
#     orbit-perturbation kick (_perturb): a few voltage resets and layer-target
#     swaps. Other runs start fresh (structured or random) on a new group.
#   * Elite states whose order is no longer above the incumbent are pruned.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_ITERS = 4000
_ELITE_CAP = 12
_WARM_PROB = 0.5


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


def _perturb(d, k, layers, S, G, rng, strength):
    """Kick an elite state: `strength` random moves (layer-target swaps or voltage resets).

    Returns fresh copies, so the elite state itself is never modified.
    """
    L = [row[:] for row in layers]
    SS = [row[:] for row in S]
    for _ in range(strength):
        l = rng.randrange(d)
        if k > 1 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            L[l][i1], L[l][i2] = L[l][i2], L[l][i1]
        else:
            SS[l][rng.randrange(k)] = rng.randrange(G)
    return L, SS


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-vertex i and B-vertex j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


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


def _anneal(d, D, k, G, Ts, Invs, layers, S, rng, deadline, iters):
    """Simulated annealing from the given state (modified in place).

    Returns (best_cost, best_layers, best_S). best_cost == 0 means a valid lift.
    """
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    best_cost = cost
    best_layers = [row[:] for row in layers]
    best_S = [row[:] for row in S]
    c0 = float(max(cost, 1))

    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
            # Structural move: swap the B-side targets of two base vertices in layer l.
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
        else:
            # Voltage move.
            i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                S[l][i] = old
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

        if cost < best_cost:
            best_cost = cost
            best_layers = [row[:] for row in layers]
            best_S = [row[:] for row in S]

    return best_cost, best_layers, best_S


def _graph_from(d, k, G, Ts, layers, S):
    """Edges of the lift from A-side darts (each B vertex has degree d by permutation layers)."""
    N = 2 * k * G
    edges = set()
    for l in range(d):
        for i in range(k):
            j = layers[l][i]
            s = S[l][i]
            for g in range(G):
                edges.add((i * G + g, (k + j) * G + int(Ts[s, g])))
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

    # Main search: elite iterated local search over bi-Cayley lifts.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    elite = {}  # key (k, m, k2, r) -> dict with cost, layers, S, k, G, Ts, Invs, N

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        # Prune elite states that can no longer beat the incumbent.
        for key in list(elite):
            if elite[key]['N'] <= best_n:
                del elite[key]

        if elite and rng.random() < _WARM_PROB:
            # Warm restart: kick a good elite state and anneal again.
            key = min(rng.sample(list(elite), min(3, len(elite))),
                      key=lambda z: elite[z]['cost'])
            e = elite[key]
            k, G = e['k'], e['G']
            layers, S = _perturb(d, k, e['layers'], e['S'], G, rng, rng.randrange(1, 4))
            cost, L2, S2 = _anneal(d, D, k, G, e['Ts'], e['Invs'], layers, S,
                                   rng, deadline, _ITERS)
        else:
            # Fresh start on a new group just above the incumbent.
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
            key = (k, m, k2, r)
            trials[k] += 1
            if rng.random() < _STRUCT_PROB:
                layers, S = _structured_init(d, k, G, Ts, rng)
            else:
                layers, S = _random_init(d, k, G, rng)
            cost, L2, S2 = _anneal(d, D, k, G, Ts, Invs, layers, S,
                                   rng, deadline, _ITERS)
            if cost == 0:
                wins[k] += 1
            e = None

        if cost == 0:
            # Valid lift found: reconstruct its edges from the group tables.
            if e is not None:
                Ts_use = e['Ts']
            else:
                Ts_use = Ts
            n_new, edges_new = _graph_from(d, k, G, Ts_use, L2, S2)
            consider(n_new, edges_new)
        else:
            # Keep the best state per group for future warm restarts.
            if e is not None:
                Ts_use, Invs_use = e['Ts'], e['Invs']
            else:
                Ts_use, Invs_use = Ts, Invs
            if key not in elite or cost < elite[key]['cost']:
                elite[key] = {'cost': cost, 'layers': L2, 'S': S2, 'k': k, 'G': G,
                              'Ts': Ts_use, 'Invs': Invs_use, 'N': 2 * k * G}
            if len(elite) > _ELITE_CAP:
                worst = max(elite, key=lambda z: elite[z]['cost'])
                del elite[worst]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
