import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Construction used here: multi-base voltage lifts over semidirect products
# Z_m x|_r Z_k (order G), with k base vertices per side and d "layers".
#
# A layer L is a bijection p_L on {0..k-1} plus a voltage s_L in G. It gives
# edges  A(i, x) -- B(p_L(i), x * s_L)  for all x in G. Each vertex then has
# degree exactly d, the graph is bipartite, and left multiplication by G is an
# automorphism, so the diameter is checked from the k A-sources and k B-sources
# at the identity only.
#
# The search engine differs from the previous one: the graph is stored as a
# numpy neighbour array and each eligibility check is a vectorised BFS from the
# 2k sources, with a simulated-annealing walk over (permutations, voltages).
# ----------------------------------------------------------------------------

BIG = 10 ** 9
ANNEAL_ITERS = 2500
_TAB = {}
_GROUPS = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N (includes cyclic Z_N)."""
    hit = _GROUPS.get(N)
    if hit is not None:
        return hit
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    if len(_GROUPS) > 256:
        _GROUPS.clear()
    _GROUPS[N] = out
    return out


def _tab(m, k, r):
    """(order, rp, invs): rp(s)[x] = x*s as a numpy array (cached), invs[s] = s^-1."""
    key = (m, k, r)
    t = _TAB.get(key)
    if t is not None:
        return t
    order, mul, inv = lib.semidirect_group(m, k, r)
    invs = [inv(s) for s in range(order)]
    cache = {}

    def rp(s):
        a = cache.get(s)
        if a is None:
            a = np.array([mul(x, s) for x in range(order)], dtype=np.int64)
            cache[s] = a
        return a

    t = (order, rp, invs)
    if len(_TAB) >= 24:
        _TAB.clear()
    _TAB[key] = t
    return t


def _nb(k, G, layers, tab):
    """Neighbour array of shape (2kG, d): A-vertices 0..kG-1, B-vertices kG..2kG-1."""
    _, rp, invs = tab
    d = len(layers)
    N = 2 * k * G
    nb = np.empty((N, d), dtype=np.int64)
    for L, (p, s) in enumerate(layers):
        Rs = rp(s)
        Ri = rp(invs[s])
        pinv = [0] * k
        for i, j in enumerate(p):
            pinv[j] = i
        for i in range(k):
            nb[i * G:(i + 1) * G, L] = k * G + p[i] * G + Rs
        for j in range(k):
            nb[k * G + j * G:k * G + (j + 1) * G, L] = pinv[j] * G + Ri
    return nb


def _dup(layers, k):
    """True if two darts share the same (i, j, s), which would create a duplicate edge."""
    seen = set()
    for p, s in layers:
        for i in range(k):
            t = (i, p[i], s)
            if t in seen:
                return True
            seen.add(t)
    return False


def _cost(nb, k, G, D):
    """Number of (source, vertex) pairs not reached within D from the 2k sources at identity."""
    N = 2 * k * G
    sources = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in sources:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            cand = nb[frontier].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            frontier = np.unique(cand)
            seen[frontier] = True
        total += N - int(seen.sum())
    return total


def _eval(layers, k, G, tab, D):
    if _dup(layers, k):
        return BIG
    return _cost(_nb(k, G, layers, tab), k, G, D)


def _anneal(d, D, k, G, tab, rng, deadline, iters):
    """Simulated annealing over layer permutations and voltages. Returns layers or None."""
    order = tab[0]
    layers = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        layers.append((p, rng.randrange(order)))
    cur = _eval(layers, k, G, tab, D)

    T0 = max(2.0, 0.05 * cur) if cur < BIG else 2.0
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        L = rng.randrange(d)
        p, s = layers[L]
        if k == 1 or rng.random() < 0.6:
            ns = rng.randrange(order)
            if ns == s:
                continue
            new = (p, ns)
        else:
            a, b = rng.sample(range(k), 2)
            q = p[:]
            q[a], q[b] = q[b], q[a]
            new = (q, s)
        old = layers[L]
        layers[L] = new
        c2 = _eval(layers, k, G, tab, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            layers[L] = old

    return layers if cur == 0 else None


def _lift_edges(layers, k, G, tab):
    nb = _nb(k, G, layers, tab)
    E = [(u, int(v)) for u in range(k * G) for v in nb[u]]
    return 2 * k * G, E


# ----------------------------------------------------------------------------
# D = 3 baseline: point-line incidence graph of PG(2, q), q + 1 <= d.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
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

    # Safe fallback: K_{d,d} has diameter 2 (and is optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: lifts with k base vertices per side over groups of order G,
    # aiming for total order 2kG above the current best.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        options = [k for k in (1, 2, 3) if n_best // (2 * k) + 1 <= moore // (2 * k)]
        if not options:
            break
        k = rng.choice(options)
        lo = n_best // (2 * k) + 1
        hi = moore // (2 * k)
        span = max(1, min(hi - lo + 1, max(4, lo // 8)))
        G = lo + rng.randrange(span)
        if G > hi or G < 2:
            continue
        gl = _groups(G)
        if not gl:
            continue
        m, k2, r = rng.choice(gl)
        tab = _tab(m, k2, r)
        layers = _anneal(d, D, k, G, tab, rng, deadline, ANNEAL_ITERS)
        if layers is not None:
            n2, e2 = _lift_edges(layers, k, G, tab)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
