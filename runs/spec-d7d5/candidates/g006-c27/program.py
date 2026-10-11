import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured baselines (kept from the parent): PG(2,q) and W(q) incidence graphs.
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
# NEW ARM: unstructured bipartite regular graphs repaired by edge switches.
#
# Start from a random d-regular bipartite graph on h + h vertices. Repeatedly
# (1) grow it by adding one vertex per side (spliced in by removing d edges and
#     reconnecting them, which keeps every degree at d), and
# (2) repair the graph with simulated annealing over degree-preserving edge
#     switches, minimising the number of vertex pairs at distance > D.
# A repaired graph with zero bad pairs is a valid candidate. Each grow step
# is validated before it is accepted, and the largest valid snapshots are
# checked with lib.is_valid before being returned.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _moore(d, D):
    try:
        return int(lib._moore_bound(d, D))
    except Exception:
        return 0


def _bad(h, d, D, nbrA, nbrB):
    """Unordered pairs at distance > D in the bipartite graph (A = 0..h-1, B = h..2h-1)."""
    n = 2 * h
    nb = np.empty((n, d), dtype=np.int64)
    nb[:h] = nbrA + h
    nb[h:] = nbrB
    W = (n + 63) // 64
    idx = np.arange(n, dtype=np.int64)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.uint64(1) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nb[:, l]]
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - total) // 2


def _init_graph(h, d, rng):
    """Random d-regular bipartite graph on h + h vertices (union of d matchings)."""
    for _ in range(50):
        nbrA = np.zeros((h, d), dtype=np.int64)
        E = np.zeros((h, h), dtype=bool)
        ok = True
        for l in range(d):
            perm = list(range(h))
            rng.shuffle(perm)
            for a in range(h):
                if E[a, perm[a]]:
                    for _t in range(50):
                        c = rng.randrange(h)
                        if not E[a, perm[c]] and not E[c, perm[a]]:
                            perm[a], perm[c] = perm[c], perm[a]
                            break
                    else:
                        ok = False
                        break
            if not ok:
                break
            for a in range(h):
                nbrA[a, l] = perm[a]
                E[a, perm[a]] = True
        if not ok:
            continue
        nbrB = np.zeros((h, d), dtype=np.int64)
        cnt = [0] * h
        for a in range(h):
            for l in range(d):
                b = int(nbrA[a, l])
                nbrB[b, cnt[b]] = a
                cnt[b] += 1
        return (h, nbrA, nbrB, E)
    return None


def _copy(state):
    h, nbrA, nbrB, E = state
    return (h, nbrA.copy(), nbrB.copy(), E.copy())


def _grow(state, d, rng):
    """Add one A vertex and one B vertex, keeping all degrees equal to d. Returns a new state or None."""
    h, nbrA, nbrB, E = state
    used_a, used_b, pairs = set(), set(), []
    tries = 0
    while len(pairs) < d and tries < 5000:
        tries += 1
        a = rng.randrange(h)
        i = rng.randrange(d)
        b = int(nbrA[a, i])
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        pairs.append((a, i, b))
    if len(pairs) < d:
        return None
    nA = np.zeros((h + 1, d), dtype=np.int64)
    nA[:h] = nbrA
    nB = np.zeros((h + 1, d), dtype=np.int64)
    nB[:h] = nbrB
    NE = np.zeros((h + 1, h + 1), dtype=bool)
    NE[:h, :h] = E
    na, nbn = h, h
    for k, (a, i, b) in enumerate(pairs):
        j = int(np.flatnonzero(nB[b] == a)[0])
        nA[a, i] = nbn          # a drops b, gains the new B vertex
        nB[b, j] = na          # b drops a, gains the new A vertex
        nA[na, k] = b
        nB[nbn, k] = a
        NE[a, b] = False
        NE[a, nbn] = True
        NE[na, b] = True
    return (h + 1, nA, nB, NE)


def _repair(state, d, D, rng, deadline, iters):
    """Annealing over degree-preserving edge switches; returns True when no pair is bad."""
    h, nbrA, nbrB, E = state
    cur = _bad(h, d, D, nbrA, nbrB)
    for t in range(iters):
        if cur == 0:
            return True
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        T = 0.8 * (1.0 - t / iters) + 0.05
        a1 = rng.randrange(h)
        a2 = rng.randrange(h)
        if a1 == a2:
            continue
        i1 = rng.randrange(d)
        i2 = rng.randrange(d)
        b1 = int(nbrA[a1, i1])
        b2 = int(nbrA[a2, i2])
        if b1 == b2 or E[a1, b2] or E[a2, b1]:
            continue
        j1 = int(np.flatnonzero(nbrB[b1] == a1)[0])
        j2 = int(np.flatnonzero(nbrB[b2] == a2)[0])
        # Apply switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        nbrA[a1, i1] = b2
        nbrA[a2, i2] = b1
        nbrB[b1, j1] = a2
        nbrB[b2, j2] = a1
        E[a1, b1] = False
        E[a2, b2] = False
        E[a1, b2] = True
        E[a2, b1] = True
        new = _bad(h, d, D, nbrA, nbrB)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            # Revert.
            nbrA[a1, i1] = b1
            nbrA[a2, i2] = b2
            nbrB[b1, j1] = a1
            nbrB[b2, j2] = a2
            E[a1, b2] = False
            E[a2, b1] = False
            E[a1, b1] = True
            E[a2, b2] = True
    return cur == 0


def _snap(state):
    h, nbrA, nbrB, _ = state
    return (h, nbrA.copy(), nbrB.copy())


def _grow_arm(d, D, rng, deadline):
    """Grow and repair; returns the last few valid snapshots (h, nbrA, nbrB)."""
    mo = _moore(d, D)
    hmax = min(2000, mo // 2) if mo else 0
    if hmax < d + 2:
        return []
    h0 = max(d + 2, min(300, hmax // 2))
    state = _init_graph(h0, d, rng)
    if state is None:
        return []
    if not _repair(state, d, D, rng, deadline, 2000):
        return []
    snaps = [_snap(state)]
    chunk = max(1, state[0] // 30)
    while time.monotonic() < deadline and state[0] < hmax:
        trial = _copy(state)
        ok = True
        for _ in range(min(chunk, hmax - trial[0])):
            trial = _grow(trial, d, rng)
            if trial is None:
                ok = False
                break
        if not ok:
            break
        if _repair(trial, d, D, rng, deadline, 2000):
            state = trial
            snaps.append(_snap(state))
            snaps = snaps[-3:]
            chunk = min(chunk * 2, max(1, state[0] // 30))
        else:
            if chunk == 1:
                break
            chunk = max(1, chunk // 2)
    return snaps


def _edges_of(h, nbrA):
    return [(a, h + int(b)) for a in range(h) for b in nbrA[a]]


# ----------------------------------------------------------------------------
# Parent arm: bi-Cayley lifts over Z_m x| Z_k2 with simulated annealing.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
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


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
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


def _cost(k, G, D, nbr):
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
    return 2 * k * N - int(_POP8[reach.view(np.uint8)].sum()) if False else \
        2 * k * N - int(sum(bin(int(x)).count("1") for x in reach))


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
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


# ----------------------------------------------------------------------------
# Driver.
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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        # Exact constructions.
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
    except Exception:
        pass

    # Phase 1 (new arm): grow-and-repair unstructured regular bipartite graphs.
    try:
        if D >= 4 and d >= 3 and time.monotonic() < deadline:
            p1 = start + 0.7 * budget
            snaps = _grow_arm(d, D, rng, p1)
            for h, nA, _nB in reversed(snaps):
                n = 2 * h
                if n <= best_n:
                    break
                e = _edges_of(h, nA)
                if lib.is_valid(n, e, d, D):
                    best = (n, e)
                    best_n = n
                    break
    except Exception:
        pass

    # Phase 2 (parent arm): semidirect-product lifts with a bandit over base sizes.
    try:
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
            res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
