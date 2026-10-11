import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Optional base construction: generalized quadrangle W(q) (diameter 4).
# Used only as a fallback candidate for D >= 4.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Main new construction: bi-Cayley graphs over finite groups.
#
# Vertices A_x and B_y for x, y in G (|G| = M). Connection set S of size d.
# Edges A_x -- B_{x*s} for s in S. Left multiplication is an automorphism, so
# the diameter is at most D iff every A-vertex and every B-vertex lies within
# distance D of A_e and of B_e. Graphs are bipartite by construction, with
# order 2M. Groups: cyclic Z_M and semidirect products Z_m x| Z_k.
# A local search over S minimises the number of unreached vertices.
# ----------------------------------------------------------------------------

def _groups(M, rng, maxg):
    """Sample group structures (order, mul, inv) of order M: cyclic plus semidirect products."""
    gl = [lib.cyclic_group(M)]
    for k in range(2, M + 1):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                gl.append(lib.semidirect_group(m, k, r))
    rng.shuffle(gl)
    return gl[:maxg]


def _table(M, mul):
    return [[mul(x, y) for y in range(M)] for x in range(M)]


def _cost(S, M, mt, invt, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_e and B_e."""
    Si = [invt[s] for s in S]
    adj = [None] * (2 * M)
    for x in range(M):
        row = mt[x]
        adj[x] = [M + row[s] for s in S]
    for y in range(M):
        row = mt[y]
        adj[M + y] = [row[t] for t in Si]
    total = 0
    for src in (0, M):
        seen = bytearray(2 * M)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for u in adj[v]:
                    if not seen[u]:
                        seen[u] = 1
                        nxt.append(u)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * M - cnt
    return total


def _edges_from(S, M, mt):
    return 2 * M, [(x, M + mt[x][s]) for x in range(M) for s in S]


def _search(M, d, D, rng, deadline):
    """Search for a connection set S in some group of order M giving diameter <= D."""
    if M < d:
        return None
    if M == d:
        # Only one choice of S: the whole group.
        gl = _groups(M, rng, 6)
        for order, mul, inv in gl:
            mt = _table(M, mul)
            invt = [inv(x) for x in range(M)]
            S = list(range(M))
            if _cost(S, M, mt, invt, D) == 0:
                return _edges_from(S, M, mt)
        return None
    for order, mul, inv in _groups(M, rng, 6):
        if time.monotonic() >= deadline:
            break
        mt = _table(M, mul)
        invt = [inv(x) for x in range(M)]
        for _restart in range(3):
            S = rng.sample(range(M), d)
            cur = _cost(S, M, mt, invt, D)
            for _it in range(400):
                if cur == 0:
                    return _edges_from(S, M, mt)
                if time.monotonic() >= deadline:
                    return None
                i = rng.randrange(d)
                g = rng.randrange(M)
                while g in S:
                    g = rng.randrange(M)
                T = S[:]
                T[i] = g
                c = _cost(T, M, mt, invt, D)
                if c <= cur or rng.random() < 0.01:
                    S, cur = T, c
            if cur == 0:
                return _edges_from(S, M, mt)
            if time.monotonic() >= deadline:
                return None
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Cheap algebraic candidates.
    try:
        if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
    except Exception:
        pass
    try:
        if D >= 4 and d >= 3:
            q = next((q for q in range(min(d - 1, 7), 1, -1) if lib.is_prime_power(q)), None)
            if q is not None:
                consider(*_gq_w(q))
    except Exception:
        pass

    if best[0] >= moore:
        return best

    # Main search: bi-Cayley graphs, trying group orders M upward from the current record.
    Mmax = moore // 2
    M = max(d, best[0] // 2 + 1)
    try:
        while M <= Mmax and time.monotonic() < deadline:
            now = time.monotonic()
            remaining = deadline - now
            budget = min(remaining, 4.0)
            res = _search(M, d, D, rng, now + budget)
            if res is not None:
                consider(res[0], res[1])
            M += 1
    except Exception:
        pass

    return best
