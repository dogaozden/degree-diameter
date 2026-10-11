import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact small constructions (kept from the parent).
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
# Lift search over Z_m x| Z_k2 (kept from the parent as a safe floor).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
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


def _lift_unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
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
    cost = _lift_unreached(k, N, reach) + _PENALTY * dupcount()
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
            c2 = _lift_unreached(k, N, r2) + _PENALTY * dupcount()
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
        c2 = _lift_unreached(k, N, r2) + _PENALTY * dupcount()
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


# ----------------------------------------------------------------------------
# NEW construction: d-regular bipartite graphs as d "layers" of perfect
# matchings between A = {0..n-1} and B = {n..2n-1}, optimised by simulated
# annealing on 2-switches (swap of targets inside one layer). The cost is the
# number of ordered vertex pairs at distance > D, computed with packed
# bitsets. The order is grown one vertex pair at a time; each growth step is
# repaired by annealing, and every success is checkpointed.
# ----------------------------------------------------------------------------

def _haar_start(n, d, rng):
    """Haar-type start: A_a ~ B_{a+s} for s in d distinct shifts mod n."""
    S = rng.sample(range(n), d)
    nbr = np.empty((d, 2 * n), dtype=np.int64)
    ar = np.arange(n, dtype=np.int64)
    for l in range(d):
        nbr[l, :n] = n + (ar + S[l]) % n
        nbr[l, n:] = (ar - S[l]) % n
    return nbr


def _mult(nbr, n):
    """M[a, b] = number of layers joining A-vertex a to B-vertex n+b."""
    M = np.zeros((n, n), dtype=np.int64)
    ar = np.arange(n)
    for l in range(nbr.shape[0]):
        np.add.at(M, (ar, nbr[l, :n] - n), 1)
    return M


def _init_bits(N, W):
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    return reach


def _bits_unreached(nbr, N, W, D, base):
    """Number of ordered pairs (v, w) with dist(v, w) > D."""
    reach = base
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        reach = new
    total = int(_POP[reach.view(np.uint16)].sum())
    return N * N - total


def _anneal(nbr, n, d, D, rng, evals, deadline):
    """Anneal 2-switches within layers. Modifies nbr in place. Returns final cost."""
    N = 2 * n
    W = (N + 63) // 64
    base = _init_bits(N, W)
    M = _mult(nbr, n)
    cost = _bits_unreached(nbr, N, W, D, base)
    for t in range(evals):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 2.0 * (1.0 - t / evals))
        l = rng.randrange(d)
        a1, a2 = rng.sample(range(n), 2)
        b1 = int(nbr[l, a1])
        b2 = int(nbr[l, a2])
        if M[a1, b2 - n] or M[a2, b1 - n]:
            continue
        nbr[l, a1] = b2
        nbr[l, a2] = b1
        nbr[l, b1] = a2
        nbr[l, b2] = a1
        M[a1, b1 - n] -= 1
        M[a2, b2 - n] -= 1
        M[a1, b2 - n] += 1
        M[a2, b1 - n] += 1
        c2 = _bits_unreached(nbr, N, W, D, base)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            nbr[l, a1] = b1
            nbr[l, a2] = b2
            nbr[l, b1] = a1
            nbr[l, b2] = a2
            M[a1, b2 - n] -= 1
            M[a2, b1 - n] -= 1
            M[a1, b1 - n] += 1
            M[a2, b2 - n] += 1
    return cost


def _grow(nbr, n, d, rng):
    """Add one A vertex (index n) and one B vertex (index 2n+1), keeping d-regularity.

    Returns (n+1, new_nbr). The input array is not modified.
    """
    N2 = 2 * (n + 1)
    new = np.empty((d, N2), dtype=np.int64)
    new[:, :n] = nbr[:, :n] + 1
    new[:, n] = 0
    new[:, n + 1:2 * n + 1] = nbr[:, n:]
    new[:, 2 * n + 1] = 0
    while True:
        ok = True
        used_a = set()
        used_b = set()
        picks = []
        for l in range(d):
            found = False
            for _ in range(50):
                a = rng.randrange(n)
                if a in used_a:
                    continue
                bo = int(new[l, a])
                if bo in used_b:
                    continue
                found = True
                break
            if not found:
                ok = False
                break
            used_a.add(a)
            used_b.add(bo)
            picks.append((a, bo))
        if ok:
            break
    for l, (a, bo) in enumerate(picks):
        new[l, a] = 2 * n + 1
        new[l, bo] = n
        new[l, n] = bo
        new[l, 2 * n + 1] = a
    return n + 1, new


def _sa_phase(d, D, rng, deadline):
    """Grow and repair a d-regular bipartite graph. Returns checkpoints [(n, nbr), ...]."""
    n = 40
    nbr = _haar_start(n, d, rng)
    cost = _anneal(nbr, n, d, D, rng, 4000, deadline)
    if cost != 0:
        return []
    cps = [(n, nbr.copy())]
    evals = 600
    while time.monotonic() < deadline:
        step = max(1, n // 60)
        cand_n, cand = n, nbr
        for _ in range(step):
            cand_n, cand = _grow(cand, cand_n, d, rng)
        c = _anneal(cand, cand_n, d, D, rng, evals, deadline)
        if c == 0:
            n, nbr = cand_n, cand
            cps.append((n, nbr.copy()))
            evals = 600
        else:
            evals = min(evals * 2, 20000)
    return cps


def _edges_from(nbr, n):
    rows = nbr[:, :n].T.tolist()
    return [(a, b) for a, row in enumerate(rows) for b in row]


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

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2 and D >= 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    # Phase 1: lift search as a safe floor (about 30% of the budget).
    lift_deadline = start + 0.3 * budget
    while time.monotonic() < lift_deadline:
        k = rng.choice(_KS)
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: grow-and-anneal bipartite regular graphs with the remaining budget.
    cps = _sa_phase(d, D, rng, deadline)

    # Verify checkpoints from the largest down; stop once no larger than best.
    verify_end = start + time_limit - 3.0
    for n_cp, nbr_cp in reversed(cps):
        if 2 * n_cp <= best_n:
            break
        if time.monotonic() > verify_end:
            break
        edges = _edges_from(nbr_cp, n_cp)
        if lib.is_valid(2 * n_cp, edges, d, D):
            best = (2 * n_cp, edges)
            best_n = 2 * n_cp
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
