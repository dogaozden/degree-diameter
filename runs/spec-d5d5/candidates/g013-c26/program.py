import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constants and caches.
# ----------------------------------------------------------------------------

KS = (1, 1, 2, 2, 3, 4, 5)         # number of base vertices per side, sampled
ANNEAL_ITERS = 1200                 # annealing steps per attempt
_BIG = 10 ** 9
_COLS_CACHE = {}
_COLS_CACHE_MAX = 10

# Non-solvable groups from PGL(2,p) / PSL(2,p), keyed by order.
_SPECIALS = {"pgl5": (5, True), "psl5": (5, False), "pgl7": (7, True), "psl7": (7, False)}
SPECIAL_ORDERS = {120: ("sp", "pgl5"), 60: ("sp", "psl5"),
                  336: ("sp", "pgl7"), 168: ("sp", "psl7")}


# ----------------------------------------------------------------------------
# Projective plane baseline for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group constructions. Each group is returned as (order, cols) where
# cols[s][g] = g * s, so that right translation by s is cols[s].
# ----------------------------------------------------------------------------

def _primitive_root(p):
    """Smallest primitive root modulo prime p."""
    for g in range(2, p):
        x, order = g, 1
        while x != 1:
            x = x * g % p
            order += 1
        if order == p - 1:
            return g
    return 1


def _perm_group(gens, n):
    """Closure of permutation generators acting on range(n). Returns (elements, index)."""
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    stack = [ident]
    while stack:
        x = stack.pop()
        for g in gens:
            y = tuple(g[t] for t in x)
            if y not in index:
                index[y] = len(elems)
                elems.append(y)
                stack.append(y)
    return elems, index


def _special_cols(name):
    """cols table for PGL(2,p) or PSL(2,p) acting on the projective line, or None."""
    p, pgl = _SPECIALS[name]
    n = p + 1
    inf = p
    g = _primitive_root(p)
    shift = tuple((x + 1) % p if x < p else inf for x in range(n))
    inv = tuple(inf if x == 0 else (0 if x == inf else (-pow(x, p - 2, p)) % p)
                for x in range(n))
    gens = [shift, inv]
    if pgl:
        mult = tuple((g * x) % p if x < p else inf for x in range(n))
        gens.append(mult)
    elems, index = _perm_group(gens, n)
    expected = p * (p * p - 1) if pgl else p * (p * p - 1) // 2
    if len(elems) != expected:
        return None
    G = len(elems)
    cols = []
    for s in range(G):
        es = elems[s]
        cols.append([index[tuple(eg[x] for x in es)] for eg in elems])
    return G, cols


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _get_cols(spec):
    """Return (order, cols) for a group spec, cached; None if unavailable."""
    if spec in _COLS_CACHE:
        return _COLS_CACHE[spec]
    res = None
    try:
        if spec[0] == "sd":
            _, m, k2, r = spec
            order, mul, _ = lib.semidirect_group(m, k2, r)
            cols = [[mul(g, s) for g in range(order)] for s in range(order)]
            res = (order, cols)
        else:
            res = _special_cols(spec[1])
    except Exception:
        res = None
    if len(_COLS_CACHE) >= _COLS_CACHE_MAX:
        _COLS_CACHE.clear()
    _COLS_CACHE[spec] = res
    return res


def _random_spec(G, rng):
    """Pick a group spec of order G, preferring nonabelian semidirect products."""
    nonab, ab = [], []
    for m, k2, r in _groups(G):
        spec = ("sd", m, k2, r)
        if k2 > 1 and r % m != 1 % m:
            nonab.append(spec)
        else:
            ab.append(spec)
    if nonab and (not ab or rng.random() < 0.9):
        return rng.choice(nonab)
    if ab:
        return rng.choice(ab)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over a group of order G.
# Vertices: A_{i,g} = i*G + g, B_{j,g} = (k+j)*G + g.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for all g.
# Each base vertex has degree d if each layer gives a permutation of base indices.
# Left translation is an automorphism, so only 2k representatives need checking.
# ----------------------------------------------------------------------------

def _init_darts(d, k, G, rng):
    """Random darts: d layers, each a permutation of base indices, with distinct (i, j, s)."""
    darts = []
    used = set()
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            j = perm[i]
            s = rng.randrange(G)
            while (i, j, s) in used:
                s = rng.randrange(G)
            used.add((i, j, s))
            darts.append((i, j, s))
    return darts


def _cost(k, G, D, darts, cols):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len(set(darts)) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        col = cols[s]
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + col[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, darts, cols):
    E = set()
    for i, j, s in darts:
        col = cols[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + col[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, cols, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer base assignments.

    Returns (n, edges) if a valid lift is found, else None.
    """
    darts = _init_darts(d, k, G, rng)
    cost = _cost(k, G, D, darts, cols)
    if cost == 0:
        return _edges(k, G, darts, cols)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.3

    for step in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + T_end

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            i, j, s = darts[idx]
            ns = rng.randrange(G)
            if ns == s:
                continue
            darts[idx] = (i, j, ns)
            c2 = _cost(k, G, D, darts, cols)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx] = (i, j, s)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            ta, tb = darts[ia], darts[ib]
            darts[ia] = (ta[0], tb[1], ta[2])
            darts[ib] = (tb[0], ta[1], tb[2])
            c2 = _cost(k, G, D, darts, cols)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia] = ta
                darts[ib] = tb

    if cost == 0:
        return _edges(k, G, darts, cols)
    return None


def _pick_config(best_n, moore, d, rng):
    """Choose (k, G, spec) aiming for total order 2*k*G > best_n and <= moore."""
    for _ in range(60):
        k = rng.choice(KS)
        lo = max(best_n // (2 * k) + 1, d, 2)
        hi = moore // (2 * k)
        if lo > hi:
            continue
        specials = [G for G in SPECIAL_ORDERS if lo <= G <= hi]
        if specials and rng.random() < 0.35:
            G = rng.choice(specials)
            return k, G, SPECIAL_ORDERS[G]
        span = hi - lo
        # Skew towards the smallest feasible order, which is easier to find.
        G = lo + min(rng.randrange(span + 1), rng.randrange(span + 1))
        spec = _random_spec(G, rng)
        if spec is None:
            continue
        return k, G, spec
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: multi-base lifts over semidirect and PGL/PSL groups.
    while best[0] < moore and time.monotonic() < deadline:
        cfg = _pick_config(best[0], moore, d, rng)
        if cfg is None:
            break
        k, G, spec = cfg
        grp = _get_cols(spec)
        if grp is None:
            continue
        order, cols = grp
        if order != G:
            continue
        res = _anneal(d, D, k, G, cols, rng, deadline, ANNEAL_ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
