import itertools
import math
import random
import time

import lib

# Bold change for D >= 3: instead of bi-Cayley / voltage-lift search, start from a
# structured d-regular bipartite graph (PG(2,q) for D = 3, the generalized quadrangle
# W(q) for D >= 4 when d-1 = q is a prime power) and grow it one vertex pair at a time.
# Each growth step inserts a new A-B pair by edge rewiring (degrees preserved), then
# repairs diameter violations with double-edge-swap simulated annealing on the count
# of vertex pairs at distance > D. Every accepted graph is checked with lib.is_valid,
# and the program falls back to K_{d,d} if anything goes wrong.

ITERS = 300        # annealing steps per growth attempt
T_HI = 1.0
T_LO = 0.1


def _cycle(D):
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def _globals(n, E):
    """Local bipartite edges (a, b) -> global ids with A = 0..n-1 and B = n..2n-1."""
    return [(a, n + b) for a, b in E]


def _bad(n, E, D):
    """Number of unordered vertex pairs at distance > D (local bipartite representation)."""
    N = 2 * n
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(n + b)
        adj[n + b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _gq_w(q):
    """Points and lines of the generalized quadrangle W(q): returns (n, E) with n points per side."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = F.inv(c)
        return tuple(F.mul(ic, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    E = []
    line_id = 0
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
            for p in L:
                E.append((p, line_id))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            line_id += 1
    if line_id != P:
        return None
    return P, E


def _start(d, D):
    """Structured d-regular bipartite starting graph (local form), or K_{d,d}."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n2, edges = lib.projective_plane_incidence(d - 1)
        m = n2 // 2
        return m, [(u, v - m) for u, v in edges]
    if D >= 4 and 3 <= d <= 9 and lib.is_prime_power(d - 1):
        res = _gq_w(d - 1)
        if res is not None:
            return res
    return d, [(a, b) for a in range(d) for b in range(d)]


def _insert(n, E, S, d, rng):
    """Add a new A vertex n and a new B vertex n, each of degree d, keeping all old degrees.

    Picks d edges (a, b) with distinct a's and distinct b's, replaces each by (n, b),
    and adds (a, n). Returns False if d such edges cannot be found.
    """
    by_a = [[] for _ in range(n)]
    for idx, (a, _) in enumerate(E):
        by_a[a].append(idx)
    order = list(range(n))
    rng.shuffle(order)
    chosen = []
    used_b = set()
    for a in order:
        if len(chosen) == d:
            break
        cands = [idx for idx in by_a[a] if E[idx][1] not in used_b]
        if cands:
            idx = rng.choice(cands)
            chosen.append(idx)
            used_b.add(E[idx][1])
    if len(chosen) < d:
        return False
    for idx in chosen:
        a, b = E[idx]
        S.discard((a, b))
        E[idx] = (n, b)
        S.add((n, b))
        E.append((a, n))
        S.add((a, n))
    return True


def _anneal(n, E, S, D, rng, iters, deadline):
    """Double-edge-swap annealing on the bad-pair count. Degrees and bipartiteness are preserved."""
    cost = _bad(n, E, D)
    m = len(E)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T_HI * (T_LO / T_HI) ** (it / max(1, iters))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1, e2 = (a1, b2), (a2, b1)
        if e1 in S or e2 in S:
            continue
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(e1)
        S.add(e2)
        E[i] = e1
        E[j] = e2
        new = _bad(n, E, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        return _cycle(D)

    moore = lib.moore_bound(d, D)  # total-vertex upper bound

    # Structured start, validated; fall back to K_{d,d}.
    n0, E0 = _start(d, D)
    if not lib.is_valid(2 * n0, _globals(n0, E0), d, D):
        n0, E0 = d, [(a, b) for a in range(d) for b in range(d)]
    best_n, best_E = n0, list(E0)

    # Growth: insert one A-B pair, then repair with annealing.
    while time.monotonic() < deadline:
        if 2 * (best_n + 1) > moore:
            break
        E2 = list(best_E)
        S2 = set(E2)
        if not _insert(best_n, E2, S2, d, rng):
            break
        n2 = best_n + 1
        cost = _anneal(n2, E2, S2, D, rng, ITERS, deadline)
        if cost == 0:
            edges = _globals(n2, E2)
            if lib.is_valid(2 * n2, edges, d, D):
                best_n, best_E = n2, E2

    edges = _globals(best_n, best_E)
    if lib.is_valid(2 * best_n, edges, d, D):
        return 2 * best_n, edges

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    return lib.haar_graph(d, range(d))
