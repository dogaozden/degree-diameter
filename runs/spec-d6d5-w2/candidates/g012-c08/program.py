import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New bold family: single-orbit Haar graphs H(G, S) over finite groups G of
# order near the record window. H(G, S) has vertices A_g, B_h (g, h in G) with
# A_g ~ B_{g s} for s in S, |S| = d. It is d-regular, bipartite, of order 2|G|.
#
# Left multiplication by G is an automorphism that is transitive on each side,
# so diameter <= D reduces to two BFS runs (from A_e and from B_e).
# Groups come from permutation representations (A6, S5 x Z3, PGL(2,7)) and from
# non-abelian semidirect products Z_m x| Z_k (which include AGL(1,19), order 342).
# S is found by simulated annealing over element swaps.
# ----------------------------------------------------------------------------


def _kdd(d):
    """K_{d,d}: diameter 2, always valid for D >= 2. Safe fallback."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _window(d, D):
    """Group-order window for Haar graphs: 2|G| should land near and above the record scale."""
    M = lib.moore_bound(d, D)
    return max(2, int(0.19 * M)), max(2, int(0.27 * M))


def _compose(p, q):
    """Product p o q of permutations given as tuples."""
    return tuple(p[i] for i in q)


def _perm_group(gens, limit):
    """Closure of permutation generators; returns (elements, index) or None if larger than limit."""
    n = len(gens[0])
    idn = tuple(range(n))
    elts = [idn]
    idx = {idn: 0}
    frontier = [idn]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = _compose(g, x)
                if y not in idx:
                    if len(elts) >= limit:
                        return None
                    idx[y] = len(elts)
                    elts.append(y)
                    nxt.append(y)
        frontier = nxt
    return elts, idx


def _table_perm(elts, idx):
    """Multiplication table M[a][b] = index of a*b for a permutation group (identity index 0)."""
    M = [[idx[_compose(a, b)] for b in elts] for a in elts]
    return len(elts), M


def _table_fn(N, mul):
    """Multiplication table from a mul(a, b) function on 0..N-1 (identity index 0)."""
    return N, [[mul(a, b) for b in range(N)] for a in range(N)]


def _inverses(N, M):
    inv = [0] * N
    for a in range(N):
        row = M[a]
        for b in range(N):
            if row[b] == 0:
                inv[a] = b
                break
    return inv


def _perm_specs():
    """Permutation generators for a few non-abelian groups with orders in the window."""
    A6 = [(1, 2, 0, 3, 4, 5), (0, 2, 3, 4, 5, 1)]                      # A6, order 360
    S5Z3 = [(1, 0, 2, 3, 4, 5, 6, 7),                                  # S5 x Z3, order 360
            (1, 2, 3, 4, 0, 5, 6, 7),
            (0, 1, 2, 3, 4, 6, 7, 5)]
    tr = tuple((x + 1) % 7 if x < 7 else 7 for x in range(8))          # PGL(2,7), order 336
    mu = tuple((3 * x) % 7 if x < 7 else 7 for x in range(8))

    def ii(x):
        if x == 7:
            return 0
        if x == 0:
            return 7
        return (-pow(x, 5, 7)) % 7

    PGL = [tr, mu, tuple(ii(x) for x in range(8))]
    return [A6, S5Z3, PGL]


def _sd_pool(lo, hi, rng):
    """Non-abelian semidirect Z_m x| Z_k with orders m*k in [lo, hi]."""
    pool = []
    for N in range(lo, hi + 1):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                rng.shuffle(rs)
                for r in rs[:2]:
                    pool.append((N, m, k, r))
    rng.shuffle(pool)
    return pool


def _build_adj(N, M, inv, S):
    """Adjacency lists of H(G, S). A_g = g, B_h = N + h."""
    adj = [None] * (2 * N)
    for g in range(N):
        row = M[g]
        adj[g] = [N + row[s] for s in S]
    invS = [inv[s] for s in S]
    for h in range(N):
        row = M[h]
        adj[N + h] = [row[t] for t in invS]
    return adj


def _unreached(adj, src, tot, D):
    """Number of vertices at distance > D from src."""
    seen = bytearray(tot)
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
    return tot - cnt


def _cost(N, M, inv, S, D):
    """Zero iff H(G, S) has diameter <= D (two BFS suffice by vertex-transitivity per side)."""
    adj = _build_adj(N, M, inv, S)
    tot = 2 * N
    return _unreached(adj, 0, tot, D) + _unreached(adj, N, tot, D)


def _search(N, M, inv, d, D, rng, deadline):
    """Anneal a connection set S (|S| = d, identity included WLOG) with diameter <= D."""
    if N - 1 < d - 1:
        return None
    others = list(range(1, N))
    while time.monotonic() < deadline:
        S = [0] + rng.sample(others, d - 1)
        c = _cost(N, M, inv, S, D)
        T = 2.0
        stale = 0
        while c > 0 and stale < 1500 and time.monotonic() < deadline:
            i = rng.randrange(1, d)
            x = rng.randrange(1, N)
            if x in S:
                continue
            S2 = S[:]
            S2[i] = x
            c2 = _cost(N, M, inv, S2, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                if c2 < c:
                    stale = 0
                S, c = S2, c2
            stale += 1
            T = max(0.3, T * 0.998)
        if c == 0:
            return S
    return None


def _haar_edges(N, M, S):
    return 2 * N, [(g, N + M[g][s]) for g in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _kdd(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane incidence meets the Moore bound for D = 3.
    if D >= 3 and 2 <= d - 1 <= 40 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: Haar graphs over groups in the window.
    if d >= 2 and time.monotonic() < deadline:
        lo, hi = _window(d, D)
        total = deadline - time.monotonic()
        per = max(2.0, min(6.0, total / 12.0))

        tasks = [("perm", g) for g in _perm_specs()]
        tasks += [("sd", t) for t in _sd_pool(lo, hi, rng)]

        for kind, spec in tasks:
            if time.monotonic() >= deadline:
                break
            if kind == "perm":
                res = _perm_group(spec, 400)
                if res is None:
                    continue
                N, M = _table_perm(*res)
            else:
                _, m, k, r = spec
                try:
                    order, mul, _ = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                N, M = _table_fn(order, mul)

            if 2 * N <= best_n or N < d:
                continue
            inv = _inverses(N, M)
            slice_end = min(deadline, time.monotonic() + per)
            S = _search(N, M, inv, d, D, rng, slice_end)
            if S is not None:
                n, e = _haar_edges(N, M, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
