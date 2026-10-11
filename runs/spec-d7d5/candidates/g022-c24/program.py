import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (used for the D = 3 and D = 4 calibration cases).
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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex has degree exactly d.
#
# NEW: warm-start orbit growth ("ladder").
#   A solved lift with k blocks is extended to k+1 blocks over the SAME group
#   by _grow_state: in each layer a random A-block a is redirected to a new
#   B-block k, and the new A-block k takes over the old target b. Degrees stay
#   d, existing voltages are kept, and only the two new darts per layer get
#   fresh voltages. The annealer then repairs the grown structure starting
#   from that warm state, instead of from a random start.
#   A ladder keeps climbing k while each rung succeeds, so one group yields a
#   chain of records of growing order 2*k*G.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KMAX = 8  # reach bitmasks use 2k bits and _POP indexes 16 bits, so 2k <= 16


def _group_of_order(G, rng):
    """Random (m, k2, r) with m*k2 = G giving Z_m x| Z_k2 (r^k2 = 1 mod m), or None."""
    by_k2 = {}
    for k2 in range(1, min(G, 36) + 1):
        if G % k2:
            continue
        m = G // k2
        if k2 == 1:
            by_k2[k2] = [(m, 1, 1)]
            continue
        if m < 2:
            continue
        opts = [(m, k2, c) for c in range(1, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if opts:
            by_k2[k2] = opts
    if not by_k2:
        return None
    k2 = rng.choice(sorted(by_k2))
    return rng.choice(by_k2[k2])


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


def _fill_nbr(k, G, Ts, Invs, d, layers, S, nbr):
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D.

    Left multiplication is an automorphism, so the 2k block starts cover all orbits.
    """
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


def _grow_state(k, G, d, layers, S, rng):
    """Extend a k-block lift to k+1 blocks (warm start for the next rung).

    In each layer: pick a random A-block a with old target b. Then A_a -> B_k
    (keeping its voltage) and A_k -> B_b (fresh random voltage). Each layer
    remains a permutation of k+1 elements, so all degrees stay d.
    """
    nl, nS = [], []
    for l in range(d):
        L = list(layers[l]) + [0]
        V = list(S[l]) + [0]
        a = rng.randrange(k)
        b = L[a]
        L[a] = k
        L[k] = b
        V[k] = rng.randrange(G)
        nl.append(L)
        nS.append(V)
    return nl, nS


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience, init=None):
    """Simulated annealing with stagnation stop. Returns (cost, layers, S); cost 0 means valid.

    init = (layers, S) warm-starts from a grown state instead of a random one.
    """
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    if init is None:
        layers = [rng.sample(range(k), k) for _ in range(d)]
        S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    else:
        layers = [list(x) for x in init[0]]
        S = [list(x) for x in init[1]]
    nbr = np.empty((d, N), dtype=np.int64)
    _fill_nbr(k, G, Ts, Invs, d, layers, S, nbr)

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
            # Layer-swap move: exchange the B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
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

    # Refresh reach state for the returned configuration when it was accepted.
    return cost, layers, S


def _edges_of(k, G, Ts, Invs, d, layers, S):
    """Materialize the lift as (n, edges) using the A-side darts."""
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    _fill_nbr(k, G, Ts, Invs, d, layers, S, nbr)
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _run_ladder(d, D, G, Ts, Invs, k0, grow, rng, deadline, consider):
    """Solve at k0, then (if grow) warm-start to k0+1, k0+2, ... while each rung succeeds."""
    iters, patience = 4000, 1200
    cost, layers, S = _search(d, D, k0, G, Ts, Invs, rng, deadline, iters, patience)
    if cost != 0:
        return
    consider(*_edges_of(k0, G, Ts, Invs, d, layers, S))
    if not grow:
        return
    k = k0
    while k < _KMAX and time.monotonic() < deadline:
        nl, nS = _grow_state(k, G, d, layers, S, rng)
        k += 1
        ok = False
        for _ in range(2):  # two warm-start attempts per rung
            cost, l2, s2 = _search(d, D, k, G, Ts, Invs, rng, deadline,
                                   iters, patience, init=(nl, nS))
            if cost == 0:
                ok = True
                break
            if time.monotonic() > deadline:
                break
        if not ok:
            break
        layers, S = l2, s2
        consider(*_edges_of(k, G, Ts, Invs, d, layers, S))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 5.0)
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

    # Exact constructions for calibration-style cases.
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

    # Main loop: pick a group whose order aims just above the current record,
    # then run a ladder (or a single rung) on it.
    while time.monotonic() < deadline:
        kt = rng.choice((3, 4, 5, 6, 7, 8))
        G_t = max(2, -(-(best_n + 2) // (2 * kt))) + rng.randrange(0, 4)
        grp = _group_of_order(G_t, rng)
        if grp is None:
            continue
        m, k2, r = grp
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        grow = rng.random() < 0.75
        k0 = max(1, kt - 2) if grow else kt
        _run_ladder(d, D, G, Ts, Invs, k0, grow, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
