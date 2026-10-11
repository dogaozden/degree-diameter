import itertools
import math
import random
import time

import lib

ITERS = 1500                 # annealing steps per (group, base multigraph) try
T_HOT = 1.5                  # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                # final annealing temperature
GROUPS_PER_ATTEMPT = 4       # groups tried per (a, N) attempt
K_PER_ROUND = 10             # candidate (a, N) orders tried per round
MAX_BUDGET = 20.0            # cap on per-attempt seconds


# ----------------------------------------------------------------------------
# Baseline families (fast, always validated by lib.is_valid before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: multi-vertex-base voltage lifts over semidirect groups.
#
# Base: a vertices on side A and a on side B, with a random bipartite multigraph
# M (row and column sums d, built as a sum of d random permutation matrices).
# Each base dart (i, j) carries m_ij distinct group voltages g. The lift has
# vertices A_{i,x} and B_{j,y} for x, y in G, with edges A_{i,x} -- B_{j,x g}.
# Left multiplication by G is an automorphism, so the diameter check only needs
# BFS from the 2a base representatives A_{i,0} and B_{j,0}.
# Order = 2 a |G|, which is a different search space from the single-base
# bi-Cayley family.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _random_base(a, d, rng):
    """Random a x a nonnegative integer matrix with all row and column sums d."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            M[i][p[i]] += 1
    return M


def _unreached(N, a, D, T, invs, S):
    """Count (source, vertex) pairs not within distance D, over all base representatives."""
    off = a * N
    V = 2 * off
    rowdarts = [[] for _ in range(a)]
    coldarts = [[] for _ in range(a)]
    for (i, j), gs in S.items():
        for g in gs:
            rowdarts[i].append((j, g))
            coldarts[j].append((i, invs[g]))
    sources = [i * N for i in range(a)] + [off + j * N for j in range(a)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < off:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in rowdarts[i]:
                        v = off + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - off, N)
                    row = T[y]
                    for i, h in coldarts[j]:
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


def _anneal(N, a, D, T, invs, M, rng, deadline):
    """Simulated annealing over the voltage sets of the base darts to zero unreached pairs."""
    S = {}
    for i in range(a):
        for j in range(a):
            if M[i][j]:
                S[(i, j)] = rng.sample(range(N), M[i][j])
    keys = list(S.keys())
    cur = _unreached(N, a, D, T, invs, S)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        lst = S[rng.choice(keys)]
        t = rng.randrange(len(lst))
        c = rng.randrange(N)
        if c in lst:
            continue
        old = lst[t]
        lst[t] = c
        v = _unreached(N, a, D, T, invs, S)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[t] = old
    if cur == 0:
        return S
    return None


def _edges(a, N, T, S):
    """Edge list and order of the lift."""
    off = a * N
    edges = []
    for (i, j), gs in S.items():
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, off + j * N + T[x][g]))
    return 2 * off, edges


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N with random base multigraphs until a valid lift is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _random_base(a, d, rng)
        S = _anneal(N, a, D, T, invs, M, rng, deadline)
        if S is not None:
            return _edges(a, N, T, S)
    return None


def _cands(d, moore, best_n):
    """(order, a, N) with order in a window just above the current best, sorted ascending."""
    window = min(moore, int(best_n * 1.25) + 24)
    out = []
    for a in (2, 3, 4):
        lo = max(d + 1, best_n // (2 * a) + 1)
        hi = min(window // (2 * a), moore // (2 * a))
        for N in range(lo, hi + 1):
            out.append((2 * a * N, a, N))
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    # Record-matching case: incidence graph of PG(2, d-1).
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

    moore = lib._moore_bound(d, D)
    budget = 0.3
    idx = 0
    while time.monotonic() < deadline:
        cands = _cands(d, moore, best_n)
        if not cands:
            break
        K = min(K_PER_ROUND, len(cands))
        for t in range(K):
            now = time.monotonic()
            if now >= deadline:
                break
            cnt, a, N = cands[(idx + t) % len(cands)]
            if cnt <= best_n:
                continue
            att = min(deadline, now + budget)
            res = _attempt(a, N, d, D, rng, att)
            if res is not None:
                n, e = res
                consider(n, e)
        idx += K
        if idx >= len(cands):
            idx = 0
            budget = min(budget * 2, MAX_BUDGET)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
