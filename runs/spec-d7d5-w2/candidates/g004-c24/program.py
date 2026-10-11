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
# Phase 1: bi-Cayley lifts over semidirect products Z_m x| Z_k2 (short search).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP16 = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
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


def _lift_reach(k, G, D, nbr, d):
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
    return 2 * k * N - int(_POP16[reach.view(np.uint16)].reshape(len(reach), 4).sum(axis=1).sum())


def _lift_search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Annealing over lift voltages. Returns (n, edges) for a valid lift, or None."""
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

    def cost_of(reach):
        unreached = 0
        for v in range(N):
            unreached += 2 * k - bin(int(reach[v])).count("1")
        return unreached + _PENALTY * dupcount()

    reach = _lift_reach(k, G, D, nbr, d)
    cost = cost_of(reach)
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
            r2 = _lift_reach(k, G, D, nbr, d)
            c2 = cost_of(r2)
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
        r2 = _lift_reach(k, G, D, nbr, d)
        c2 = cost_of(r2)
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
# Phase 2 (bold, different construction): general bipartite graph repair.
#
# State: a d-regular bipartite graph stored in combined indices. A-side vertex i
# has id i, B-side vertex j has id CAP + j. nb[x] lists the d neighbours of x.
#
# Growth: add one A and one B vertex by removing d disjoint edges (a_i, y_i)
# and attaching the new A vertex to all y_i and the new B vertex to all a_i.
# Degrees stay exactly d.
#
# Repair: simulated annealing with degree-preserving double-edge swaps. The cost
# is the number of ordered vertex pairs at distance > D, computed with packed
# bitsets in numpy. Half of the moves are aimed at a vertex that still has
# unreached partners.
# ----------------------------------------------------------------------------

def _reach_full(nb, D, W):
    M = nb.shape[0]
    idx = np.arange(M)
    reach = np.zeros((M, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _eval(nb, h, CAP, D, W):
    act = np.concatenate([np.arange(h), CAP + np.arange(h)])
    reach = _reach_full(nb, D, W)
    rows = np.ascontiguousarray(reach[act])
    pc = _POP16[rows.view(np.uint16)].sum(axis=1)
    rowdef = (2 * h) - pc
    return int(rowdef.sum()), rowdef, act


def _swap(nb, a1, s1, a2, s2, b1, b2):
    """Set nb[a1,s1]=b2, nb[a2,s2]=b1 and fix the B-side rows (requires b1=old nb[a1,s1], b2=old nb[a2,s2])."""
    nb[a1, s1] = b2
    nb[a2, s2] = b1
    r = nb[b1]
    r[r == a1] = a2
    r = nb[b2]
    r[r == a2] = a1


def _init_state(n, edges, d, CAP):
    h = n // 2
    M = 2 * CAP
    nb = np.tile(np.arange(M, dtype=np.int64)[:, None], (1, d))
    deg = [[] for _ in range(n)]
    for u, v in edges:
        deg[u].append(v)
        deg[v].append(u)
    for x in range(n):
        if len(deg[x]) != d:
            return None
        cx = x if x < h else CAP + (x - h)
        nb[cx, :] = [y if y < h else CAP + (y - h) for y in deg[x]]
    return nb, h


def _grow(nb, h, CAP, d, rng):
    if h + 1 > CAP:
        return None
    used_b = set()
    pairs = []
    order = list(range(h))
    rng.shuffle(order)
    for a in order:
        if len(pairs) == d:
            break
        s = rng.randrange(d)
        y = int(nb[a, s])
        if y in used_b:
            continue
        used_b.add(y)
        pairs.append((a, s, y))
    if len(pairs) < d:
        return None
    newA = h
    newB = CAP + h
    for a, s, y in pairs:
        nb[a, s] = newB
        r = nb[y]
        r[r == a] = newA
    nb[newA, :] = [y for _, _, y in pairs]
    nb[newB, :] = [a for a, _, _ in pairs]
    return h + 1


def _anneal(nb, h, CAP, d, D, rng, deadline):
    W = (2 * CAP + 63) // 64
    cost, rowdef, act = _eval(nb, h, CAP, D, W)
    T = 1.5
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        defect_idx = np.flatnonzero(rowdef > 0)
        if rng.random() < 0.5 and defect_idx.size:
            u = int(act[defect_idx[rng.randrange(defect_idx.size)]])
            if u >= CAP:
                a1 = int(nb[u, rng.randrange(d)])
            else:
                a1 = u
        else:
            a1 = rng.randrange(h)
        s1 = rng.randrange(d)
        a2 = rng.randrange(h)
        s2 = rng.randrange(d)
        b1 = int(nb[a1, s1])
        b2 = int(nb[a2, s2])
        if a1 == a2 or b1 == b2:
            continue
        if (nb[a1] == b2).any() or (nb[a2] == b1).any():
            continue
        _swap(nb, a1, s1, a2, s2, b1, b2)
        c2, rd2, act2 = _eval(nb, h, CAP, D, W)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost, rowdef, act = c2, rd2, act2
        else:
            _swap(nb, a1, s1, a2, s2, b2, b1)
    return True


def _extract(nb, h, CAP):
    edges = []
    for a in range(h):
        for b in nb[a]:
            edges.append((a, h + int(b) - CAP))
    return 2 * h, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Phase 1: short lift search to get a strong regular starting graph.
    try:
        lift_deadline = start + 0.4 * budget
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        while time.monotonic() < lift_deadline:
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
            res = _lift_search(d, D, k, G, Ts, Invs, rng, lift_deadline, 3000)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
    except Exception:
        pass

    # Phase 2: grow the best regular graph and repair with annealing.
    if d >= 3 and D >= 2:
        try:
            CAP = best_n // 2 + 60
            st = _init_state(best_n, best[1], d, CAP)
            if st is not None:
                nb, h = st
                while time.monotonic() < deadline:
                    h2 = _grow(nb, h, CAP, d, rng)
                    if h2 is None:
                        break
                    h = h2
                    if not _anneal(nb, h, CAP, d, D, rng, deadline):
                        break
                    n, e = _extract(nb, h, CAP)
                    consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
