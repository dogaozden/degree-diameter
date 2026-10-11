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


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over a general finite group given by its multiplication table.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d.
#
# NEW in this version: the group family is no longer only Z_m x| Z_k.
# Main family: affine groups Aff(Z_m) = { x -> u*x + b : u a unit mod m },
# order m*phi(m), generally NON-metabelian-by-cyclic and not a split extension
# of a cyclic group by a cyclic group with a faithful action. Half of the
# bandit arms draw from it. The other arms use the semidirect Z_m x| Z_k2.
#
# Search: simulated annealing over voltages and per-layer target swaps, with
# the cost = number of unreached (block representative, vertex) pairs at
# distance > D, plus a penalty for duplicate edges.
# Safe fallback: K_{d,d} (diameter 2) and the projective plane incidence graph.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_ARMS = [("aff", 1), ("aff", 2), ("aff", 3),
         ("semi", 1), ("semi", 2), ("semi", 3), ("semi", 4)]


def _affine_candidates(max_m=300):
    """Sorted list of (order, m) for the affine groups Aff(Z_m) with order m*phi(m)."""
    out = []
    for m in range(3, max_m):
        units = [u for u in range(1, m) if math.gcd(u, m) == 1]
        out.append((m * len(units), m))
    out.sort()
    return out


def _affine_mul(m):
    """Multiplication table M[g, h] = g*h for Aff(Z_m).

    Element (b, u) is the map x -> u*x + b, coded as b*phi + index(u).
    (b1,u1)*(b2,u2) = (b1 + u1*b2, u1*u2), i.e. composition g(h(x)).
    """
    units = [u for u in range(1, m) if math.gcd(u, m) == 1]
    phi = len(units)
    G = m * phi
    uarr = np.array(units, dtype=np.int64)
    uidx = np.full(m, -1, dtype=np.int64)
    uidx[uarr] = np.arange(phi, dtype=np.int64)
    idx = np.arange(G, dtype=np.int64)
    b = idx // phi
    u = uarr[idx % phi]
    prod_u = (u[:, None] * u[None, :]) % m
    prod_b = (b[:, None] + u[:, None] * b[None, :]) % m
    M = prod_b * phi + uidx[prod_u]
    return G, M


def _semidirect_mul(m, k2, r):
    """Multiplication table for Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return M


def _tables_from_mul(M):
    """Return (G, Ts, Invs): Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = M.shape[0]
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    x = np.arange(G, dtype=np.int64)
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _sample_semidirect(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16])
        m = max(2, -(-target // k2))
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


def _structured_init(d, k, G, Ts, rng):
    """Geometric-progression start for groups with identity index 0 (semidirect family)."""
    x = rng.randrange(1, G)
    powers = [0]
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
    """Write layer l's neighbours for A-vertex block i and B-vertex block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    """Unreached (block representative, vertex) pairs over all 2k block representatives."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, structured):
    """Simulated annealing over voltages and per-layer target swaps. Returns (n, edges) or None."""
    N = 2 * k * G
    if structured and rng.random() < _STRUCT_PROB:
        layers, S = _structured_init(d, k, G, Ts, rng)
    else:
        layers, S = _random_init(d, k, G, rng)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
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
            continue

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

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D <= 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions for D = 3 and D = 4 (fast, returned when they are records).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 5 or time.monotonic() >= deadline:
        pass
    # Main search: bandit over (family, base size).
    AFF = _affine_candidates()
    trials = {a: 0 for a in _ARMS}
    wins = {a: 0 for a in _ARMS}

    def pick_arm():
        if rng.random() < 0.2:
            return rng.choice(_ARMS)
        return max(_ARMS, key=lambda a: (wins[a] + 1) / (trials[a] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        arm = pick_arm()
        fam, k = arm
        lo = best_n // (2 * k) + 1
        cap = best_n + max(40, best_n // 8)
        hi = cap // (2 * k)
        if hi < lo:
            continue

        if fam == "aff":
            tol = max(3, lo // 12)
            window = [c for c in AFF if lo <= c[0] <= min(hi, lo + tol)]
            if not window:
                continue
            G_target, m = rng.choice(window)
            G, M = _affine_mul(m)
            G, Ts, Invs = _tables_from_mul(M)
            structured = False
        else:
            tgt = max(2, lo + rng.randrange(0, max(2, lo // 8 + 1)))
            g = _sample_semidirect(tgt, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Ts, Invs = _tables_from_mul(_semidirect_mul(m, k2, r))
            structured = True

        if 2 * k * G <= best_n or 2 * k * G > cap:
            continue

        trials[arm] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 5000, structured)
        if res is not None:
            wins[arm] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
