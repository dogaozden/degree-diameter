import math
import random
import time

import lib

_BIG = 10 ** 9


class _Best:
    """Holds the best valid graph found so far; offer() only accepts strict, valid improvements."""

    def __init__(self, n, edges, d, D):
        self.n = n
        self.edges = list(edges)
        self.d = d
        self.D = D

    def offer(self, n, edges):
        if n > self.n and lib.is_valid(n, edges, self.d, self.D):
            self.n = n
            self.edges = list(edges)


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family A: bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2,
# with k A-orbits and k B-orbits, annealed on the exact diameter cost.
# ----------------------------------------------------------------------------

def _group_options(Gp, cache):
    """All (m, k2, r) with m * k2 = Gp that give a semidirect product Z_m x| Z_k2."""
    if Gp in cache:
        return cache[Gp]
    opts = []
    for k2 in range(1, Gp + 1):
        if Gp % k2:
            continue
        m = Gp // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    cache[Gp] = opts
    return opts


def _tables(m, k2, r):
    """Return (order, cols) with cols[s][g] = g * s in the semidirect product."""
    Gp, mul, _inv = lib.semidirect_group(m, k2, r)
    cols = [[mul(g, s) for g in range(Gp)] for s in range(Gp)]
    return Gp, cols


def _unreached(adj, N, src, D):
    """Number of vertices not within distance D of src."""
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return N - cnt


def _gadj(k, Gp, cols, P, V, d):
    """Adjacency of the bi-Cayley lift. A_{i,g} ~ B_{P[L][i], g * V[L][i]} for every layer L."""
    N = 2 * k * Gp
    adj = [[] for _ in range(N)]
    for L in range(d):
        pl = P[L]
        vl = V[L]
        for i in range(k):
            j = pl[i]
            col = cols[vl[i]]
            base_a = i * Gp
            base_b = (k + j) * Gp
            for g in range(Gp):
                a = base_a + g
                b = base_b + col[g]
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _gcost(k, Gp, cols, P, V, d, D):
    """Total unreached (representative, vertex) pairs. Zero iff the lift is valid."""
    for i in range(k):
        seen = set()
        for L in range(d):
            key = (P[L][i], V[L][i])
            if key in seen:
                return _BIG
            seen.add(key)
    adj = _gadj(k, Gp, cols, P, V, d)
    N = 2 * k * Gp
    reps = [i * Gp for i in range(k)] + [(k + j) * Gp for j in range(k)]
    return sum(_unreached(adj, N, src, D) for src in reps)


def _ganneal(d, D, k, Gp, cols, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer target permutations."""

    def init():
        P, V = [], []
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            P.append(p)
            V.append([rng.randrange(Gp) for _ in range(k)])
        return P, V

    P, V = init()
    cost = _gcost(k, Gp, cols, P, V, d, D)
    tries = 0
    while cost >= _BIG and tries < 200:
        tries += 1
        P, V = init()
        cost = _gcost(k, Gp, cols, P, V, d, D)
    if cost >= _BIG:
        return None

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.2, 2.0 * (1.0 - it / iters))
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.7:
            i = rng.randrange(k)
            old = V[L][i]
            new = rng.randrange(Gp)
            if new == old:
                continue
            V[L][i] = new
            c2 = _gcost(k, Gp, cols, P, V, d, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                V[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]
            c2 = _gcost(k, Gp, cols, P, V, d, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                P[L][a], P[L][b] = P[L][b], P[L][a]

    if cost != 0:
        return None
    adj = _gadj(k, Gp, cols, P, V, d)
    N = 2 * k * Gp
    edges = [(a, b) for a in range(N) for b in adj[a] if b > a]
    return N, edges


def _group_phase(best, d, D, rng, deadline):
    cache = {}
    tabs = {}
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3])
        Gp = -(-(best.n + 1) // (2 * k)) + rng.randrange(0, 2)
        opts = _group_options(Gp, cache)
        if not opts:
            continue
        key = rng.choice(opts)
        if key not in tabs:
            if len(tabs) > 300:
                tabs.clear()
            tabs[key] = _tables(*key)
        Gp2, cols = tabs[key]
        if Gp2 != Gp:
            continue
        res = _ganneal(d, D, k, Gp, cols, rng, deadline, 1500)
        if res is not None:
            best.offer(*res)


# ----------------------------------------------------------------------------
# Family B (bold, unstructured): simple d-regular bipartite graphs repaired by
# double edge switches under simulated annealing on the number of bad pairs.
# ----------------------------------------------------------------------------

def _random_regular(N, d, rng):
    """Simple d-regular bipartite graph with N + N vertices, as a list of (a, b) with 0 <= a, b < N."""
    if d > N:
        return None
    for _ in range(3000):
        E = set()
        ok = True
        for _L in range(d):
            p = list(range(N))
            rng.shuffle(p)
            for a in range(N):
                e = (a, p[a])
                if e in E:
                    ok = False
                    break
                E.add(e)
            if not ok:
                break
        if ok:
            return list(E)
    return None


def _bad(n, adj, D):
    """Number of unordered pairs at distance more than D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _dswitch(E, Eset, adj, N, i1, i2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it twice undoes it."""
    a1, b1 = E[i1]
    a2, b2 = E[i2]
    Eset.discard((a1, b1))
    Eset.discard((a2, b2))
    Eset.add((a1, b2))
    Eset.add((a2, b1))
    adj[a1].remove(N + b1)
    adj[N + b1].remove(a1)
    adj[a2].remove(N + b2)
    adj[N + b2].remove(a2)
    adj[a1].append(N + b2)
    adj[N + b2].append(a1)
    adj[a2].append(N + b1)
    adj[N + b1].append(a2)
    E[i1] = (a1, b2)
    E[i2] = (a2, b1)


def _usa(N, d, D, rng, deadline):
    """Anneal a random d-regular bipartite graph with N vertices per side toward diameter D."""
    init = _random_regular(N, d, rng)
    if init is None:
        return None
    E = list(init)
    Eset = set(E)
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    cost = _bad(n, adj, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.15, 1.5 * (1.0 - (time.monotonic() - start) / span))
        i1 = rng.randrange(len(E))
        i2 = rng.randrange(len(E))
        if i1 == i2:
            continue
        a1, b1 = E[i1]
        a2, b2 = E[i2]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        _dswitch(E, Eset, adj, N, i1, i2)
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _dswitch(E, Eset, adj, N, i1, i2)
    if cost == 0:
        return n, [(a, N + b) for a, b in E]
    return None


def _unstructured_phase(best, d, D, rng, deadline):
    while time.monotonic() < deadline:
        N = best.n // 2 + 1
        slice_end = min(deadline, time.monotonic() + 12.0)
        res = _usa(N, d, D, rng, slice_end)
        if res is not None:
            best.offer(*res)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    base_n, base_e = lib.haar_graph(d, range(d))
    best = _Best(base_n, base_e, d, D)

    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            best.offer(*pg)

    # Calibration cases already at the Moore bound return immediately.
    if best.n >= lib._moore_bound(d, D):
        return best.n, best.edges

    # Structured bi-Cayley lifts first, then the unstructured repair search.
    group_deadline = min(deadline, start + 0.35 * time_limit)
    _group_phase(best, d, D, rng, group_deadline)
    _unstructured_phase(best, d, D, rng, deadline)

    if not lib.is_valid(best.n, best.edges, d, D):
        return base_n, base_e
    return best.n, best.edges
