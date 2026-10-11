import random
import time

import lib

# This version generalises the arc extension. Each extra A-vertex is joined
# to a set T of lines that covers every point, with |T| <= d, and the sets
# are pairwise intersecting. Each line lies in at most s = d-q-1 of the sets.
# A mirror B-vertex is joined to the same index set T as points, which keeps
# the diameter at 3 and the graph bipartite. Pencils at conic points are the
# special case that gives the old arc bound (k = q+1). A randomized greedy
# with restarts searches for larger families, and the conic family is kept as
# a fallback. Every candidate is checked with lib.is_valid.


def _pg_index(q):
    """Return (m, edges, nbr, cov) for PG(2, q) in index space.

    nbr[x] lists indices j with dot(x, j) = 0. The relation is symmetric, so
    nbr[x] is both the set of lines through point x and the set of points on
    line x. cov[x] is the bitmask of nbr[x].
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    cov = [0] * m
    for x in range(m):
        c = 0
        for j in nbr[x]:
            c |= 1 << j
        cov[x] = c
    return m, edges, nbr, cov


def _conic_init(q):
    """Conic (plus nucleus for even q) as index set, using the same ordering as lib.projective_points."""
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _kub(m, q, s):
    """Upper bound on family size: pairwise intersection plus line-load counting."""
    pairs = s * (s - 1) // 2 * m
    k = 1
    while (k + 1) * k // 2 <= pairs:
        k += 1
    return min(k, max(1, s * m // (q + 1)))


def _try_add(m, cov, d, s, fam_k, load, owners, rng, tries):
    """Try to build one new covering set T that meets every existing set, uses only indices with load < s, and has |T| <= d."""
    full = (1 << m) - 1
    cand = [j for j in range(m) if load[j] < s]
    for _ in range(tries):
        unc = full
        hit = [False] * fam_k
        unhit = fam_k
        T = []
        used = set()
        while True:
            if unc == 0 and unhit == 0:
                return T
            if len(T) >= d:
                break
            bj, bsc = -1, -1.0
            for j in cand:
                if j in used:
                    continue
                g = (cov[j] & unc).bit_count()
                h = 0
                for i in owners[j]:
                    if not hit[i]:
                        h += 1
                if g == 0 and h == 0:
                    continue
                sc = g + 3.0 * h + rng.random()
                if sc > bsc:
                    bsc, bj = sc, j
            if bj < 0:
                break
            unc &= ~cov[bj]
            for i in owners[bj]:
                if not hit[i]:
                    hit[i] = True
                    unhit -= 1
            T.append(bj)
            used.add(bj)
    return None


def _family_search(m, cov, d, s, rng, deadline, target):
    """Randomized greedy with restarts. Returns the largest family found."""
    best = []
    while time.monotonic() < deadline and len(best) < target:
        fam = []
        load = [0] * m
        owners = [[] for _ in range(m)]
        while time.monotonic() < deadline:
            T = _try_add(m, cov, d, s, len(fam), load, owners, rng, 6)
            if T is None:
                break
            idx = len(fam)
            fam.append(T)
            for j in T:
                load[j] += 1
                owners[j].append(idx)
        if len(fam) > len(best):
            best = fam
    return best


def _family_graph(m, edges, fam):
    """PG(2,q) incidence plus an A-vertex and a B-vertex per family set."""
    k = len(fam)
    E = list(edges)
    for a, T in enumerate(fam):
        x = 2 * m + a
        for j in T:
            E.append((x, m + j))  # A-vertex joined to lines in T (A is point-side)
    for a, T in enumerate(fam):
        b = 2 * m + k + a
        for i in T:
            E.append((i, b))      # B-vertex joined to points in T (B is line-side)
    return 2 * m + 2 * k, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Plain projective plane for the largest prime power q with q + 1 <= d.
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if pg_qs:
            consider(*lib.projective_plane_incidence(pg_qs[0]))

        # Plans: prime powers q with s = d-q-1 >= 1 whose bound could beat the current best.
        plans = []
        for q in range(2, d - 1):
            if not lib.is_prime_power(q) or q > 23:
                continue
            s = d - q - 1
            if s < 1:
                continue
            m, edges, nbr, cov = _pg_index(q)
            kub = _kub(m, q, s)
            if 2 * m + 2 * kub > best_n:
                plans.append((q, m, s, kub, edges, nbr, cov))

        total = sum(p[1] for p in plans) or 1
        span = max(0.0, deadline - time.monotonic())
        for q, m, s, kub, edges, nbr, cov in plans:
            slice_end = time.monotonic() + span * m / total
            # Conic pencils: the old arc construction, kept as a fallback.
            fam_c = [list(nbr[P]) for P in _conic_init(q)]
            consider(*_family_graph(m, edges, fam_c))
            fam = _family_search(m, cov, d, s, rng, slice_end, kub)
            if fam:
                consider(*_family_graph(m, edges, fam))

    return best
