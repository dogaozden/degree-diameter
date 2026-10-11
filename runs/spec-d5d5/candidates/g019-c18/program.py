import itertools
import math
import random
import time

import lib

ITERS = 2500               # annealing steps per (k, N, group) attempt
GROUPS_PER_ATTEMPT = 6     # groups tried per attempt
SLICE = 2.5                # seconds per attempt before moving to another (k, N)


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
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


def _best_gq(d):
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit group lifts (a substantially different family from the parent).
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}.
# Group G of order N (semidirect Z_m x| Z_k). Vertex A_{i,x} and B_{j,y}.
# For each block (i,j) a set S_ij of group elements with
#     A_{i,x} ~ B_{j, x*g}  for g in S_ij.
# Row and column sums of |S_ij| equal d, so both sides are d-regular.
# Left multiplication is an automorphism, so the diameter is decided by
# eccentricities of the 2k representatives A_{i,0} and B_{j,0}.
# Total order: 2*k*N, bipartite by construction.
# ----------------------------------------------------------------------------

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


def _lists(k, sets, invs):
    """Adjacency generators: aout[i] = [(j, g)], bin_[j] = [(i, g^-1)]."""
    aout = [[] for _ in range(k)]
    bin_ = [[] for _ in range(k)]
    for i in range(k):
        for j in range(k):
            for g in sets[i][j]:
                aout[i].append((j, g))
                bin_[j].append((i, invs[g]))
    return aout, bin_


def _unreached(N, k, T, aout, bin_, D):
    """Total (source, vertex) pairs not within distance D over the 2k representatives."""
    kN = k * N
    M = 2 * kN
    total = 0
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    for src in sources:
        seen = bytearray(M)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in aout[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, h in bin_[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += M - count
    return total


def _search(N, k, d, D, T, invs, rng, iters, deadline):
    """Anneal the block sets to zero unreached pairs; return sets or None."""
    sizes = [[0] * k for _ in range(k)]
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            sizes[i][perm[i]] += 1
    sets = [[rng.sample(range(N), sizes[i][j]) for j in range(k)] for i in range(k)]
    cells = [(i, j) for i in range(k) for j in range(k) if sizes[i][j] > 0]
    aout, bin_ = _lists(k, sets, invs)
    cur = _unreached(N, k, T, aout, bin_, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i, j = rng.choice(cells)
        t = rng.randrange(len(sets[i][j]))
        c = rng.randrange(N)
        if c in sets[i][j]:
            continue
        old = sets[i][j][t]
        sets[i][j][t] = c
        aout2, bin2 = _lists(k, sets, invs)
        v = _unreached(N, k, T, aout2, bin2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            aout, bin_ = aout2, bin2
        else:
            sets[i][j][t] = old
    return sets if cur == 0 else None


def _edges(N, k, T, aout):
    kN = k * N
    edges = []
    for i in range(k):
        for x in range(N):
            for j, g in aout[i]:
                edges.append((i * N + x, kN + j * N + T[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching calibration: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    mb = lib._moore_bound(d, D)

    while time.monotonic() < deadline:
        # Admissible base sizes k (2kN vertices) that could still beat best_n.
        options = []
        for k in (1, 2, 3, 4):
            cap = mb // (2 * k)
            base = best_n // (2 * k) + 1
            if base <= cap and cap > d:
                options.append((k, base, cap))
        if not options:
            break
        k, base, cap = rng.choice(options)
        hi = min(base + 3, cap)
        N = rng.randint(base, hi)

        groups = _groups(N)
        rng.shuffle(groups)
        slice_end = min(deadline, time.monotonic() + SLICE)

        for m, kk, r in groups[:GROUPS_PER_ATTEMPT]:
            if time.monotonic() >= slice_end:
                break
            _, mul, inv = lib.semidirect_group(m, kk, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            invs = [inv(g) for g in range(N)]
            sets = _search(N, k, d, D, T, invs, rng, ITERS, slice_end)
            if sets is not None:
                aout, _ = _lists(k, sets, invs)
                consider(2 * k * N, _edges(N, k, T, aout))
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
