import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective planes (D = 3), Araujo-Pardo & Lopez (D = 3), and
# generalized quadrangles W(q) (D = 4). These are the safe starting points.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
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


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over a finite group G of order N.
#   A-vertices x in G, B-vertices y in G (B_y has id N + y).
#   Edge A_x -- B_{x*s} for every s in S, |S| = d.
# Left multiplication by g is an automorphism (A_x -> A_{gx}, B_y -> B_{gy}),
# so the diameter is at most D iff
#   - every vertex is within D of A_e   (covers A-A, A-B pairs), and
#   - every vertex is within D of B_e   (covers B-B pairs).
# Each check is one bounded BFS, so the search is cheap.
# ----------------------------------------------------------------------------

def _cost(N, S, mt, ivs, D):
    """Number of (source, vertex) pairs left unreached within D, for sources A_e and B_e."""
    Sinv = [ivs[s] for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = mt[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = mt[v - N]
                    for t in Sinv:
                        w = row[t]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - sum(seen)
    return total


def _anneal(N, d, D, mt, ivs, rng, deadline):
    """Find a d-subset S of G with zero cost, by annealing single-element swaps."""
    S = rng.sample(range(N), d)
    cur = _cost(N, S, mt, ivs, D)
    temp = 1.0
    stall = 0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        T2 = S[:]
        T2[i] = g
        c = _cost(N, T2, mt, ivs, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            if c < cur:
                stall = 0
            S, cur = T2, c
        stall += 1
        if stall > 2000:
            S = rng.sample(range(N), d)
            cur = _cost(N, S, mt, ivs, D)
            stall = 0
        temp = max(0.2, temp * 0.9995)
    return S if cur == 0 else None


def _candidate_groups(N, rng, limit=8):
    """Non-abelian semidirect products Z_m x| Z_k of order N (shuffled), then cyclic as a last resort."""
    found = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                found.append((m, k, r))
    rng.shuffle(found)
    groups = [lib.semidirect_group(m, k, r) for (m, k, r) in found[:limit]]
    groups.append(lib.cyclic_group(N))
    return groups


def _search(d, D, N0, deadline, rng, consider):
    """Ascending search over group orders N; stop at the first order that fails."""
    cap = lib.moore_bound(d, D) // 2
    N = N0
    while N <= cap and time.monotonic() < deadline:
        ok = False
        for order, mul, inv in _candidate_groups(N, rng):
            if time.monotonic() >= deadline:
                break
            mt = [[mul(x, y) for y in range(N)] for x in range(N)]
            ivs = [inv(x) for x in range(N)]
            per_group = min(deadline, time.monotonic() + 4.0)
            S = _anneal(N, d, D, mt, ivs, rng, per_group)
            if S is not None:
                edges = [(x, N + mt[x][s]) for x in range(N) for s in S]
                consider(2 * N, edges)
                ok = True
                break
        if not ok:
            break
        N += 1


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.8 * T
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

    if D == 2:
        return best
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    if best[0] >= lib.moore_bound(d, D):
        return best

    if D == 3:
        b = _best_pg(d)
        if b is not None:
            consider(b[0], b[1])
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    else:
        q = next((q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            try:
                consider(*_gq_w(q))
            except Exception:
                pass

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Bold search: bi-Cayley graphs over semidirect products, starting just above the base.
    N0 = max(d, best[0] // 2 + 1)
    try:
        _search(d, D, N0, deadline, rng, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
