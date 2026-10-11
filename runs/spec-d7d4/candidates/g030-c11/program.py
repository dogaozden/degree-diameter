import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and lines of the symplectic space PG(3,q).
# Incidence graph has diameter 4 and degree q+1, order 2(q+1)(q^2+1).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _pad(P, edges, d, rng):
    """Add opposite-side edges between vertices with spare degree (keeps bipartite, distances only shrink)."""
    edges = list(edges)
    n = 2 * P
    deg = [0] * n
    have = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        have.add((min(u, v), max(u, v)))
    left = [v for v in range(P) if deg[v] < d]
    right = [v for v in range(P, n) if deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (a, b) not in have]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Non-abelian Haar graphs.
# Group G of order N, connection set S with identity in S (WLOG).
# Vertices a_x (x in G) and b_y; a_x ~ b_{x s} for s in S.
# G acts regularly on each side, so diameter <= D iff every vertex is within D
# of a_e and of b_e. Degree is |S| = d exactly.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect products Z_m x| Z_k (order N), including cyclic and direct products."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    return out


def _deficit(N, tbl, invl, S, D):
    """Number of (root, vertex) pairs NOT within distance D of a_e or b_e. Zero iff diameter <= D."""
    Sinv = [invl[s] for s in S]
    missing = 0
    for root in (0, 1):
        seen = [set(), set()]
        seen[root].add(0)
        frontier = [0]
        side = root
        for _ in range(D):
            if not frontier:
                break
            nxt = set()
            if side == 0:
                for x in frontier:
                    row = tbl[x]
                    for s in S:
                        nxt.add(row[s])
            else:
                for y in frontier:
                    row = tbl[y]
                    for si in Sinv:
                        nxt.add(row[si])
            other = 1 - side
            new = nxt - seen[other]
            seen[other] |= new
            frontier = new
            side = other
        missing += 2 * N - len(seen[0]) - len(seen[1])
    return missing


def _search(N, d, D, tbl, invl, rng, deadline):
    """Simulated-annealing style hill climb over connection sets S (size d, containing identity 0)."""
    if N < d or d < 2:
        return None
    elems = list(range(1, N))
    while time.monotonic() < deadline:
        S = [0] + rng.sample(elems, d - 1)
        cur = _deficit(N, tbl, invl, S, D)
        T = 0.6
        stall = 0
        while cur > 0 and time.monotonic() < deadline and stall < 400:
            i = rng.randrange(1, d)
            cand = rng.randrange(1, N)
            if cand in S:
                stall += 1
                continue
            old = S[i]
            S[i] = cand
            new = _deficit(N, tbl, invl, S, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                stall = 0 if new < cur else stall + 1
                cur = new
            else:
                S[i] = old
                stall += 1
        if cur == 0:
            return S
    return None


def _haar_edges(N, tbl, S):
    return [(x, N + tbl[x][s]) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Known optimal / strong base constructions.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
    if D == 4 and d >= 3:
        qs = [q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)]
        if qs:
            n, e = _gq_w(qs[0])
            e = _pad(n // 2, e, d, rng)
            consider(n, e)

    # Bold stage: search non-abelian Haar graphs over semidirect products.
    if d >= 3 and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        hi = moore // 2
        cache = {}
        while time.monotonic() < deadline and lo <= hi:
            u = rng.random()
            N = hi - int((hi - lo) * u * u)  # biased toward large orders
            if N not in cache:
                cache[N] = _groups(N)
            gl = cache[N]
            if not gl:
                continue
            m, k, r = rng.choice(gl)
            _, mul, inv = lib.semidirect_group(m, k, r)
            tbl = [[mul(x, y) for y in range(N)] for x in range(N)]
            invl = [inv(x) for x in range(N)]
            slice_end = min(deadline, time.monotonic() + 1.0)
            S = _search(N, d, D, tbl, invl, rng, slice_end)
            if S is not None:
                edges = _haar_edges(N, tbl, S)
                if 2 * N > best[0] and lib.is_valid(2 * N, edges, d, D):
                    best = (2 * N, edges)
                    lo = N + 1

    return best
