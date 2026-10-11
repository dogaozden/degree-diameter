import itertools
import math
import random
import time

import lib

# New construction in this version: multi-orbit bi-lifts. The vertex set is
# A_i x G and B_j x G for i, j < o, with G a semidirect product Z_m x| Z_k.
# A dart (i, j, g) joins A_(i,x) to B_(j, x*g). The multiplicity matrix
# (row and column sums d) fixes the degrees. Searching over o = 2 or 3 orbits
# reaches orders 2*o*N that the single-orbit bi-Cayley search cannot reach.

MAX_GROUPS_PER_ATTEMPT = 16
ITERS = 900
T_HOT = 1.2
T_COLD = 0.1


# ----------------------------------------------------------------------------
# Baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group enumeration.
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


# ----------------------------------------------------------------------------
# Multiplicity matrices for the orbit base graph.
# ----------------------------------------------------------------------------

def _mult_matrices(o, d):
    """All o x o matrices of nonnegative integers with every row and column summing to d.

    For o > 1 every entry is at least 1, so the base multigraph is connected.
    """
    out = []
    mat = [[0] * o for _ in range(o)]
    rowrem = [d] * o
    colrem = [d] * o

    def rec(idx):
        if idx == o * o:
            out.append([row[:] for row in mat])
            return
        i, j = divmod(idx, o)
        hi = min(rowrem[i], colrem[j])
        if j == o - 1:
            vals = [rowrem[i]]
        else:
            vals = range(0, hi + 1)
        for v in vals:
            if v > hi:
                continue
            if o > 1 and v == 0:
                continue
            mat[i][j] = v
            rowrem[i] -= v
            colrem[j] -= v
            rec(idx + 1)
            rowrem[i] += v
            colrem[j] += v
        mat[i][j] = 0

    rec(0)
    return out


# ----------------------------------------------------------------------------
# Evaluation: unreached (source, vertex) pairs for the o-orbit bi-lift.
# Left multiplication by G is an automorphism, so one source per layer
# (A_i at identity, B_j at identity) decides the diameter.
# ----------------------------------------------------------------------------

def _unreached(N, o, T, invs, blocks, D):
    base = o * N
    V = 2 * base
    dart_from = [[] for _ in range(o)]   # for A-orbit i: (j, g)
    dart_into = [[] for _ in range(o)]   # for B-orbit j: (i, g^-1)
    for i, j, gs in blocks:
        for g in gs:
            dart_from[i].append((j, g))
            dart_into[j].append((i, invs[g]))
    sources = [i * N for i in range(o)] + [base + j * N for j in range(o)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dart_from[i]:
                        v = base + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base, N)
                    row = T[y]
                    for i, h in dart_into[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, o, T, invs, mat, D, rng, iters, deadline):
    """Anneal the voltages (distinct inside each block) to zero unreached pairs."""
    blocks = []
    for i in range(o):
        for j in range(o):
            c = mat[i][j]
            if c > 0:
                blocks.append([i, j, rng.sample(range(N), c)])
    cur = _unreached(N, o, T, invs, blocks, D)
    for it in range(iters):
        if cur == 0:
            return blocks
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        b = blocks[rng.randrange(len(blocks))]
        idx = rng.randrange(len(b[2]))
        c = rng.randrange(N)
        if c in b[2]:
            continue
        old = b[2][idx]
        b[2][idx] = c
        v = _unreached(N, o, T, invs, blocks, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            b[2][idx] = old
    return blocks if cur == 0 else None


def _attempt(N, o, d, D, rng, deadline):
    """Try groups of order N and multiplicity matrices until a diameter-D lift is found."""
    mats = _mult_matrices(o, d)
    if not mats:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        mat = rng.choice(mats)
        blocks = _anneal(N, o, T, invs, mat, D, rng, ITERS, deadline)
        if blocks is not None:
            return T, blocks
    return None


def _edges(N, o, T, blocks):
    """Edges of the lift: A_(i,x) = i*N + x, B_(j,y) = o*N + j*N + y."""
    base = o * N
    edges = []
    for i, j, gs in blocks:
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, base + j * N + T[x][g]))
    return edges


def _search_orbits(o, d, D, rng, k_deadline, state, consider):
    """Ascending search over N for the o-orbit lift; the budget doubles on failure."""
    Nmax = lib._moore_bound(d, D) // (2 * o)
    N = max(d + 1, state["best"][0] // (2 * o) + 1)
    budget = 0.5
    while N <= Nmax and time.monotonic() < k_deadline:
        att = min(k_deadline, time.monotonic() + budget)
        res = _attempt(N, o, d, D, rng, att)
        if res is None:
            budget = min(budget * 2, 30.0)
            continue
        T, blocks = res
        consider(2 * o * N, _edges(N, o, T, blocks))
        N = max(N + 1, state["best"][0] // (2 * o) + 1)
        budget = 0.5


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = {"best": (1, [])}

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return state["best"]

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
        return state["best"]

    moore = lib._moore_bound(d, D)
    orbit_counts = [o for o in (2, 1, 3) if 2 * o <= moore and (o == 1 or o <= d)]
    for idx, o in enumerate(orbit_counts):
        now = time.monotonic()
        if now >= deadline:
            break
        k_deadline = now + (deadline - now) / (len(orbit_counts) - idx)
        _search_orbits(o, d, D, rng, k_deadline, state, consider)

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
