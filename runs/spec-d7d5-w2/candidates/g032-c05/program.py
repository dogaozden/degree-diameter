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


def _keep(best, n, e, d, D):
    """Return (n, e) if it is larger than best and valid, else best."""
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


# ----------------------------------------------------------------------------
# Phase B: bi-Cayley lifts over semidirect products Z_m x| Z_k2 (safe search).
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_PENALTY = 1000


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
    Ts = np.ascontiguousarray(M.T)
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
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

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
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


def _bicayley_phase(best, d, D, rng, phase_deadline):
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < phase_deadline:
        best_n = best[0]
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
        res = _search(d, D, k, G, Ts, Invs, rng, phase_deadline, 4000)
        if res is not None:
            wins[k] += 1
            best = _keep(best, res[0], res[1], d, D)
    return best


# ----------------------------------------------------------------------------
# Phase A (bold): unstructured simulated annealing on d-regular bipartite
# graphs. Degree-preserving edge switches; cost = number of ordered vertex
# pairs at distance > D, computed with Python big-int reach bitsets.
# ----------------------------------------------------------------------------

def _cost(n, nb, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _layer(h, adjA, rng):
    """Random permutation of range(h) avoiding existing edges adjA[a]; None if repair fails."""
    perm = list(range(h))
    rng.shuffle(perm)
    for _ in range(100):
        conf = [a for a in range(h) if perm[a] in adjA[a]]
        if not conf:
            return perm
        for a in conf:
            j = rng.randrange(h)
            if perm[a] not in adjA[j] and perm[j] not in adjA[a]:
                perm[a], perm[j] = perm[j], perm[a]
    return None


def _init_graph(h, d, rng):
    n = 2 * h
    for _ in range(30):
        adjA = [set() for _ in range(h)]
        ok = True
        for _l in range(d):
            perm = _layer(h, adjA, rng)
            if perm is None:
                ok = False
                break
            for a in range(h):
                adjA[a].add(perm[a])
        if ok:
            nb = [set() for _ in range(n)]
            E = []
            for a in range(h):
                for b in adjA[a]:
                    nb[a].add(h + b)
                    nb[h + b].add(a)
                    E.append((a, h + b))
            return E, nb
    return None


def _anneal(n, d, D, rng, deadline):
    h = n // 2
    init = _init_graph(h, d, rng)
    if init is None:
        return None
    E, nb = init
    cost = _cost(n, nb, D)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            break
        T = 1.5 * (1.0 - (now - t0) / span) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, v1 = E[i]
        a2, v2 = E[j]
        if a1 == a2 or v1 == v2 or v2 in nb[a1] or v1 in nb[a2]:
            continue
        nb[a1].discard(v1); nb[v1].discard(a1)
        nb[a2].discard(v2); nb[v2].discard(a2)
        nb[a1].add(v2); nb[v2].add(a1)
        nb[a2].add(v1); nb[v1].add(a2)
        c2 = _cost(n, nb, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            E[i] = (a1, v2)
            E[j] = (a2, v1)
        else:
            nb[a1].discard(v2); nb[v2].discard(a1)
            nb[a2].discard(v1); nb[v1].discard(a2)
            nb[a1].add(v1); nb[v1].add(a1)
            nb[a2].add(v2); nb[v2].add(a2)
    if cost != 0:
        return None
    return [(a, v) for a, v in E]


def _sa_phase(best, d, D, rng, deadline):
    cap = min(lib.moore_bound(d, D), 3000)
    step = 16
    while time.monotonic() < deadline - 0.5:
        best_n = best[0]
        n_try = best_n + step
        if n_try % 2:
            n_try += 1
        if n_try > cap:
            break
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(1.0, remaining * 0.5))
        res = _anneal(n_try, d, D, rng, slice_end)
        if res is not None:
            new = _keep(best, n_try, res, d, D)
            if new[0] == n_try:
                best = new
                step = 16
                continue
        step = max(2, step // 2)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # Exact projective-plane construction (calibration cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _keep(best, pg[0], pg[1], d, D)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Secure a strong baseline first, then attempt larger unstructured graphs.
    phase_b_deadline = start + 0.45 * budget
    best = _bicayley_phase(best, d, D, rng, phase_b_deadline)
    best = _sa_phase(best, d, D, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
