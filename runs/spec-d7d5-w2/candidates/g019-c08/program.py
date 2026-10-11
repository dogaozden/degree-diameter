import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: Haar graphs over abelian groups (not necessarily cyclic).
# Vertices A_g = g, B_h = G + h. Edge A_g ~ B_{g+s} for s in S, with 0 in S.
# Translation and the swap A_g <-> B_{-g} make A_0 a witness for the whole graph,
# so diameter <= D iff BFS from A_0 reaches all 2G vertices within D steps.
# ----------------------------------------------------------------------------

def _factor(m):
    f = {}
    p = 2
    while p * p <= m:
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
        p += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


def _partitions(e, maxpart=None):
    if maxpart is None:
        maxpart = e
    if e == 0:
        yield []
        return
    for first in range(min(e, maxpart), 0, -1):
        for rest in _partitions(e - first, first):
            yield [first] + rest


def _random_abelian_sizes(m, rng):
    """Random cyclic decomposition of an abelian group of order m (m >= 2)."""
    sizes = []
    for p, e in _factor(m).items():
        choice = rng.choice(list(_partitions(e)))
        sizes.extend(p ** a for a in choice)
    return sizes


def _abelian_tables(sizes):
    """Return (G, Add, neg) for the direct product of cyclic groups of the given sizes."""
    strides = []
    s = 1
    for c in sizes:
        strides.append(s)
        s *= c
    G = s
    idx = np.arange(G, dtype=np.int64)
    Add = np.zeros((G, G), dtype=np.int64)
    neg = np.zeros(G, dtype=np.int64)
    for st, c in zip(strides, sizes):
        ci = (idx // st) % c
        Add += ((ci[:, None] + ci[None, :]) % c) * st
        neg += ((-ci) % c) * st
    return G, Add, neg


def _uncovered(G, Add, neg, S, D):
    """Number of vertices of the Haar graph not within distance D of A_0."""
    negS = neg[S]
    vis = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
    vis[0][0] = True
    front = np.array([0], dtype=np.int64)
    side = 0
    for _ in range(D):
        if side == 0:
            cand = Add[np.ix_(front, S)].ravel()      # A_g -> B_{g+s}
        else:
            cand = Add[np.ix_(front, negS)].ravel()   # B_h -> A_{h-s}
        cand = np.unique(cand)
        cand = cand[~vis[1 - side][cand]]
        vis[1 - side][cand] = True
        front = cand
        side = 1 - side
        if front.size == 0:
            break
    return 2 * G - int(vis[0].sum()) - int(vis[1].sum())


def _anneal_abelian(G, Add, neg, d, D, rng, deadline, iters):
    """Simulated annealing over S (0 fixed in S). Returns S as an array, or None."""
    S = np.array([0] + rng.sample(range(1, G), d - 1), dtype=np.int64)
    cost = _uncovered(G, Add, neg, S, D)
    for t in range(iters):
        if cost == 0:
            return S
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        temp = 0.3 + 2.0 * (1.0 - t / iters)
        i = rng.randrange(1, d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _uncovered(G, Add, neg, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[i] = old
    return S if cost == 0 else None


def _haar_from_S(G, Add, S):
    edges = []
    for g in range(G):
        for s in S:
            edges.append((g, G + int(Add[g, s])))
    return 2 * G, edges


def _abelian_phase(d, D, rng, deadline, consider):
    """Search abelian Haar graphs with order above the current best. Returns nothing; uses consider."""
    lo = None
    while time.monotonic() < deadline:
        if lo is None:
            lo = consider.best_n() // 2 + 1
        m = lo + rng.randrange(0, 6)
        if m < 2:
            m = 2
        sizes = _random_abelian_sizes(m, rng)
        if not sizes:
            continue
        G, Add, neg = _abelian_tables(sizes)
        if G <= d:
            continue
        S = _anneal_abelian(G, Add, neg, d, D, rng, deadline, 6000)
        if S is None:
            continue
        n, e = _haar_from_S(G, Add, S)
        if consider(n, e):
            lo = G + 1


# ----------------------------------------------------------------------------
# Parent family: bi-Cayley lifts over semidirect products Z_m x| Z_k2 with k blocks.
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


def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _extend(n, edges, d, D, rng, deadline, max_fail=300):
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
            fails = 0
        else:
            fails += 1
    return n, edges


class _Best:
    """Holds the best valid graph found so far; consider() validates before accepting."""

    def __init__(self, n, e, d, D):
        self.n, self.e, self.d, self.D = n, e, d, D

    def best_n(self):
        return self.n

    def __call__(self, n, e):
        if n > self.n and lib.is_valid(n, e, self.d, self.D):
            self.n, self.e = n, e
            return True
        return False


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    abelian_deadline = start + 0.5 * budget
    search_deadline = start + 0.8 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb = lib.haar_graph(d, range(d))
    best = _Best(fb[0], fb[1], d, D)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best.n, best.e

    # New family: abelian Haar lifts.
    if d >= 2 and D >= 2:
        _abelian_phase(d, D, rng, abelian_deadline, best)

    # Parent family: semidirect bi-Cayley search with a bandit over block counts.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best.n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best.n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
        if res is not None:
            if best(res[0], res[1]):
                wins[k] += 1

    try:
        n2, e2 = _extend(best.n, best.e, d, D, rng, deadline)
        if n2 > best.n:
            best(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best.n, best.e, d, D):
        best = _Best(fb[0], fb[1], d, D)
    return best.n, best.e
