import math
import random
import time

import numpy as np

import lib

# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8        # groups tried per bi-Cayley order before moving on
CLIMB_ITERS = 400     # hill-climb steps per group
ANNEAL_ITERS = 3000   # annealing steps per multi-base attempt
ANNEAL_PATIENCE = 500 # stop an annealing run after this many steps without a new best cost
BAND_EXTRA = 12       # sweep window above the lower bound for bi-Cayley orders
BIG = 10 ** 9
_GRP_CACHE = {}


# ----------------------------------------------------------------------------
# New helper 1: vectorised reach-cost for voltage lifts.
#
# Every dart of a lift is a bijection between one A-block and one B-block, so
# one BFS layer can be expanded with plain fancy indexing (no duplicate targets
# inside a single dart). All representatives are propagated at once as a
# boolean matrix R[source, vertex]. Each step computes the radius-(t+1) balls
# R_{t+1} = R_t OR N(R_t). The cost is the number of (source, vertex) pairs
# still outside distance D, so zero means diameter <= D from every block
# representative, which by left-translation covers the whole graph.
# ----------------------------------------------------------------------------

def _cost(nv, pairs, sources, D):
    """Unreached (source, vertex) pairs after D rounds. Zero means every block is covered."""
    R = np.zeros((len(sources), nv), dtype=bool)
    R[np.arange(len(sources)), np.asarray(sources, dtype=np.int64)] = True
    for _ in range(D):
        R2 = R.copy()
        for a, b in pairs:
            R2[:, b] |= R[:, a]
            R2[:, a] |= R[:, b]
        R = R2
    return len(sources) * nv - int(np.count_nonzero(R))


# ----------------------------------------------------------------------------
# New helper 2: semidirect product Z_m x|_r Z_k with vectorised right
# multiplication. rmul(s)[x] = x * s is computed once per s as a numpy array,
# which avoids building the full G x G multiplication table in Python.
# ----------------------------------------------------------------------------

class _Grp:
    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.N = m * k
        self.ar = np.arange(self.N, dtype=np.int64)
        self.a = self.ar // k
        self.b = self.ar % k
        self.pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
        self.cache = {}

    def rmul(self, s):
        """Array t with t[x] = x * s, using (a,b)(c,d) = (a + r^b c, b + d)."""
        v = self.cache.get(s)
        if v is None:
            c, d = divmod(s, self.k)
            v = ((self.a + self.pw[self.b] * c) % self.m) * self.k + (self.b + d) % self.k
            self.cache[s] = v
        return v


def _get_grp(m, k, r):
    key = (m, k, r)
    g = _GRP_CACHE.get(key)
    if g is None:
        if len(_GRP_CACHE) > 64:
            _GRP_CACHE.clear()
        g = _Grp(m, k, r)
        _GRP_CACHE[key] = g
    return g


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N and r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley search (one base vertex per side): hill-climb on the connection set.
# A_x ~ B_{x g} for g in S. WLOG the identity lies in S (relabel B).
# ----------------------------------------------------------------------------

def _climb(grp, d, D, rng, iters, deadline):
    N = grp.N
    ar = grp.ar

    def cost_of(S):
        if len(set(S)) < d:
            return BIG
        pairs = [(ar, N + grp.rmul(s)) for s in S]
        return _cost(2 * N, pairs, [0, N], D)

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = cost_of(S)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = cost_of(S2)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Multi-base voltage lift (k base vertices per side) annealed over darts.
# Dart (i, j, s) joins A-block i to B-block j by g -> g*s. Each layer L holds
# one dart per A-block, through a permutation of B-blocks, so every vertex has
# degree d. Distinct (i, j, s) keeps the graph simple.
# ----------------------------------------------------------------------------

def _multi_cost(k, grp, darts, D, sources):
    G = grp.N
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
    pairs = [(i * G + grp.ar, (k + j) * G + grp.rmul(s)) for i, j, s in darts]
    return _cost(2 * k * G, pairs, sources, D)


def _anneal(d, D, k, grp, rng, deadline, iters):
    G = grp.N
    sources = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    cost = _multi_cost(k, grp, darts, D, sources)
    best_cost = cost
    stall = 0
    T0 = max(1.0, 0.05 * min(cost, 10 ** 5))

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline or stall > ANNEAL_PATIENCE:
            break
        T = max(0.3, T0 * (0.02 ** (it / max(1, iters))))

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _multi_cost(k, grp, darts, D, sources)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _multi_cost(k, grp, darts, D, sources)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

        if cost < best_cost:
            best_cost = cost
            stall = 0
        else:
            stall += 1

    return darts if cost == 0 else None


def _multi_edges(k, G, grp, darts):
    E = set()
    for i, j, s in darts:
        t = grp.rmul(s)
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(t[g])))
    return 2 * k * G, list(E)


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of PG(2, q), q the largest prime power with q+1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}: diameter 2, always valid
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or best[0] >= moore:
        return best

    sweep_next = None
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]

        if rng.random() < 0.6:
            # Bi-Cayley lift on a group of order N has 2N vertices. Sweep N upward
            # from the smallest order that would beat the current best.
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            if sweep_next is None or sweep_next < lo or sweep_next > lo + BAND_EXTRA:
                sweep_next = lo
            N = sweep_next
            sweep_next += 1
            groups = _groups(N)
            rng.shuffle(groups)
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                grp = _get_grp(m, k2, r)
                S = _climb(grp, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    edges = []
                    for s in S:
                        t = grp.rmul(s)
                        edges.extend((x, N + int(t[x])) for x in range(N))
                    consider(2 * N, edges)
                    break
        else:
            # Multi-base lift with k base vertices per side over a group of order G.
            k = rng.choice((2, 3))
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            if G < 2:
                continue
            m, k2, r = rng.choice(_groups(G))
            grp = _get_grp(m, k2, r)
            darts = _anneal(d, D, k, grp, rng, deadline, ANNEAL_ITERS)
            if darts is not None:
                n2, e2 = _multi_edges(k, G, grp, darts)
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
