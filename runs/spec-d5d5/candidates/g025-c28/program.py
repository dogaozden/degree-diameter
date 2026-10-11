import itertools
import math
import random
import time

import lib

ITERS = 1000          # annealing steps per (group, cell-set) try
T_HOT = 1.2           # initial annealing temperature (in unreached-pair units)
T_COLD = 0.08         # final annealing temperature
GROUPS_PER_N = 8      # groups tried per attempt


# ----------------------------------------------------------------------------
# Safe baseline families (fast, validated before use).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley search.
#
# Group G = Z_m x|_r Z_k of order N. Vertices A^i_x and B^j_y for
# i, j in 0..p-1 and x, y in G. Edges: A^i_x -- B^j_{x s} for s in S[i][j],
# where |S[i][j]| = c[i][j]. Row sums and column sums of c equal d, so the
# graph is d-regular and bipartite with 2*p*N vertices. Left multiplication
# by G is an automorphism, so eccentricities from A^i_0 and B^j_0 suffice.
#
# With p = 1 this is the single-orbit bi-Cayley family. With p = 2 the
# construction uses two orbits per side, a genuinely different search space.
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


def _cost(p, N, T, invs, S, D):
    """Total count of (source, vertex) pairs not within distance D over all orbit sources."""
    pN = p * N
    V = 2 * pN
    fwd = [[(j, s) for j in range(p) for s in S[i][j]] for i in range(p)]
    back = [[(i, invs[s]) for i in range(p) for s in S[i][j]] for j in range(p)]
    sources = [i * N for i in range(p)] + [pN + j * N for j in range(p)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < pN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, s in fwd[i]:
                        v = pN + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - pN, N)
                    row = T[y]
                    for i, si in back[j]:
                        v = i * N + row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(p, N, T, invs, c, D, rng, deadline):
    """Simulated annealing over the connection sets to reach zero unreached pairs."""
    cells = [(i, j, c[i][j]) for i in range(p) for j in range(p) if c[i][j] > 0]
    S = [[[] for _ in range(p)] for _ in range(p)]
    for i, j, k in cells:
        S[i][j] = rng.sample(range(N), k)
    cur = _cost(p, N, T, invs, S, D)
    for it in range(ITERS):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        i, j, k = cells[rng.randrange(len(cells))]
        t = rng.randrange(k)
        new = rng.randrange(N)
        if new in S[i][j]:
            continue
        old = S[i][j][t]
        S[i][j][t] = new
        v = _cost(p, N, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][t] = old
    return S if cur == 0 else None


def _attempt(p, N, c, D, rng, deadline):
    """Try groups of order N until a connection family with diameter <= D is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_N]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(p, N, T, invs, c, D, rng, deadline)
        if S is not None:
            return T, S
    return None


def _edges(p, N, T, S):
    """Edge list for the multi-orbit lift: A^i_x = i*N + x, B^j_y = p*N + j*N + y."""
    pN = p * N
    edges = []
    for i in range(p):
        for j in range(p):
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, pN + j * N + T[x][s]))
    return 2 * pN, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    def finish():
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
        return best[0], best[1]

    # Calibration: incidence graph of PG(2, d-1) meets the bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return finish()

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
        return finish()

    Mmoore = lib._moore_bound(d, D)
    a_opts = sorted({a for a in (d // 2, (d + 1) // 2) if 1 <= a <= d - 1})

    attempt = 0
    budget = 6.0
    while time.monotonic() < deadline:
        # Stop when neither two-orbit nor one-orbit families can beat the best order.
        if all(best[0] // (2 * q) + 1 > Mmoore // (2 * q) for q in (1, 2)):
            break

        slot = attempt % 3
        cycle_idx = attempt // 3
        attempt += 1
        p = 2 if slot < 2 else 1
        if p == 2:
            if not a_opts:
                continue
            a = a_opts[cycle_idx % len(a_opts)]
            c = [[a, d - a], [d - a, a]]
        else:
            c = [[d]]

        lo = best[0] // (2 * p) + 1
        hi = Mmoore // (2 * p)
        if lo > hi:
            continue
        N = min(hi, lo + rng.randrange(0, 6))

        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(p, N, c, D, rng, att_deadline)
        if res is not None:
            T, S = res
            n, e = _edges(p, N, T, S)
            consider(n, e)
        budget = min(25.0, budget * 1.03)

    return finish()
