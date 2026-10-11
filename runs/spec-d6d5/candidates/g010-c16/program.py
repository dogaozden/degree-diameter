import math
import random
import time

import lib


def _unreached(N, adj, src, D):
    """Number of vertices not within distance D of src (BFS, early exit)."""
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
    return N - count


class _Group:
    """Finite group given by its multiplication, with cached right-translation permutations."""

    def __init__(self, order, mul):
        self.order = order
        self.mul = mul
        self._perm = {}

    def perm(self, s):
        p = self._perm.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.order)]
            self._perm[s] = p
        return p


def _sample_group(G, rng):
    """Random metacyclic group Z_m x| Z_k2 of order G (r = 1 gives the abelian product)."""
    divs = [k2 for k2 in range(1, G + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs[:12]:
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(200):
                cand = rng.randrange(1, m)
                if math.gcd(cand, m) == 1 and pow(cand, k2, m) == 1 % m:
                    r = cand
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return _Group(order, mul)
    return None


def _build_adj(k, G, V, grp):
    """Adjacency of the bi-Cayley lift: A_{i,g} ~ B_{j, g*s} for s in V[i][j]."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i in range(k):
        bi = i * G
        for j in range(k):
            bj = (k + j) * G
            for s in V[i][j]:
                p = grp.perm(s)
                for g in range(G):
                    a = bi + g
                    b = bj + p[g]
                    adj[a].append(b)
                    adj[b].append(a)
    return N, adj


def _cost(k, G, V, grp, D):
    """Unreached (representative, vertex) pairs. Representatives are the identities of each layer,
    which suffices because left multiplication is an automorphism of the lift."""
    N, adj = _build_adj(k, G, V, grp)
    total = 0
    for i in range(k):
        total += _unreached(N, adj, i * G, D)
        total += _unreached(N, adj, (k + i) * G, D)
    return total


def _edges(k, G, V, grp):
    E = []
    for i in range(k):
        for j in range(k):
            for s in V[i][j]:
                p = grp.perm(s)
                for g in range(G):
                    E.append((i * G + g, (k + j) * G + p[g]))
    return 2 * k * G, E


def _anneal(d, D, k, G, grp, rng, deadline, iters):
    """Metropolis search over voltages. Each (i,j) block holds c = d // k distinct voltages,
    so every vertex has degree d and the graph is simple and bipartite."""
    c = d // k
    V = [[rng.sample(range(G), c) for _ in range(k)] for _ in range(k)]
    cur = _cost(k, G, V, grp, D)
    T = 1.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.998)
        i = rng.randrange(k)
        j = rng.randrange(k)
        t = rng.randrange(c)
        old = V[i][j][t]
        new = rng.randrange(G)
        while new in V[i][j]:
            new = rng.randrange(G)
        V[i][j][t] = new
        c2 = _cost(k, G, V, grp, D)
        limit = cur - T * math.log(1.0 - rng.random())
        if c2 <= limit:
            cur = c2
        else:
            V[i][j][t] = old
    if cur == 0:
        return V, 0
    return None, cur


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, degree d).
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    if D >= 3:
        # Projective plane incidence graph of PG(2, q) with q + 1 <= d (diameter 3).
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    n_pg, e_pg = lib.projective_plane_incidence(q)
                    consider(n_pg, e_pg)
                except Exception:
                    pass
                break
        if D == 3:
            # Araujo-Pardo & Lopez record family for d = q + 2.
            q = d - 2
            if q >= 3 and lib.is_prime_power(q):
                try:
                    n_ar, e_ar = lib.araujo_lopez_graph(q)
                    consider(n_ar, e_ar)
                except Exception:
                    pass
        if best[0] >= moore:
            return best

    # Main search: bi-Cayley lifts over metacyclic groups, with k sides per layer
    # where k divides d (so each block carries d // k voltages).
    ks = [k for k in range(1, d + 1) if d % k == 0]
    while time.monotonic() < deadline:
        if best[0] >= moore:
            break
        k = rng.choice(ks)
        c = d // k
        lo = max(c + 1, best[0] // (2 * k) + 1)
        G = rng.randint(lo, lo + max(4, lo // 40))
        grp = _sample_group(G, rng)
        if grp is None or grp.order < c + 1:
            continue
        iters = 1200 if k <= 2 else 600
        V, _ = _anneal(d, D, k, grp.order, grp, rng, deadline, iters)
        if V is not None:
            n, e = _edges(k, grp.order, V, grp)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
