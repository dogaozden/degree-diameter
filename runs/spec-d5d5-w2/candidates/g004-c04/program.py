import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search parameters.
# ----------------------------------------------------------------------------
MAX_GROUPS_PER_ATTEMPT = 8    # groups tried per (p, N) attempt
ITERS = 400                   # annealing steps per (group, connection data) try
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW_FRAC = 0.95            # search orders in [WINDOW_FRAC * top, top] first
BUDGET_START = 0.6            # seconds per attempt in the first pass
BUDGET_CAP = 3.0              # cap on per-attempt seconds as passes fail
PMAX = 3                      # maximum number of orbits per side


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
# NEW IDEA: multi-orbit bi-Cayley lifts.
#
# The parent uses one orbit per side (p = 1): A_x -- B_{x s}, s in S, |S| = d.
# Here each side is split into p orbits over a group G of order N:
#   A^i_x (i < p, x in G)  and  B^j_y (j < p, y in G),
#   A^i_x -- B^j_{x s} for every s in S[i][j].
# The connection pattern is a p x p matrix M of set sizes with every row sum
# and column sum equal to d, so every vertex has degree d. The support of M must
# be connected, so the graph is connected. Order is 2 p N, which lets the search
# hit orders the single-orbit family cannot, for example 4N with p = 2 or 6N
# with p = 3. Left multiplication by G is an automorphism, so the diameter is
# decided by eccentricities from the 2p representatives A^i_e and B^j_e.
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


def _connected(M, p):
    """True if the bipartite support of the p x p matrix M is connected."""
    parent = list(range(2 * p))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for i in range(p):
        for j in range(p):
            if M[i][j]:
                parent[find(i)] = find(p + j)
    root = find(0)
    return all(find(v) == root for v in range(2 * p))


def _size_matrix(p, d, rng):
    """Random p x p matrix of nonnegative integers with all row/column sums d and connected support.

    Built as a sum of d random permutation matrices, which fixes all sums at d.
    """
    for _ in range(100):
        M = [[0] * p for _ in range(p)]
        for _ in range(d):
            perm = list(range(p))
            rng.shuffle(perm)
            for i in range(p):
                M[i][perm[i]] += 1
        if _connected(M, p):
            return M
    return None


def _unreached(N, p, T, S, SI, D):
    """Count (source, vertex) pairs not within distance D, over the 2p orbit representatives.

    Vertex ids: A^i_x -> i*N + x; B^j_y -> p*N + j*N + y.
    """
    base_b = p * N
    V = 2 * base_b
    sources = [i * N for i in range(p)] + [base_b + j * N for j in range(p)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base_b:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j in range(p):
                        b = base_b + j * N
                        for g in S[i][j]:
                            v = b + row[g]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - base_b, N)
                    row = T[y]
                    for i in range(p):
                        a = i * N
                        for h in SI[i][j]:
                            v = a + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, p, T, invs, M, D, rng, iters, deadline):
    """Anneal the connection sets S[i][j] (sizes M[i][j]) to zero unreached pairs."""
    S = [[rng.sample(range(N), M[i][j]) if M[i][j] else [] for j in range(p)]
         for i in range(p)]
    SI = [[[invs[g] for g in S[i][j]] for j in range(p)] for i in range(p)]
    cells = [(i, j) for i in range(p) for j in range(p) if M[i][j]]
    cur = _unreached(N, p, T, S, SI, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(cells)
        k = rng.randrange(len(S[i][j]))
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][k]
        S[i][j][k] = c
        SI[i][j][k] = invs[c]
        v = _unreached(N, p, T, S, SI, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][k] = old
            SI[i][j][k] = invs[old]
    return S if cur == 0 else None


def _attempt(N, p, M, D, rng, deadline):
    """Try groups of order N for the p-orbit family; return (T, S) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, p, T, invs, M, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _graph(N, p, T, S):
    """Materialise the p-orbit bi-Cayley graph: A^i_x -- B^j_{x g} for g in S[i][j]."""
    base_b = p * N
    edges = []
    for i in range(p):
        for j in range(p):
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, base_b + j * N + T[x][g]))
    return 2 * p * N, edges


def _candidates(d, lo, hi):
    """All (p, N) pairs with order 2pN in [lo, hi] and N >= d."""
    out = []
    for p in range(1, PMAX + 1):
        step = 2 * p
        for N in range(max(d, -(-lo // step)), hi // step + 1):
            out.append((p, N))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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

    # Order window: the Moore bound is far above what is reachable, so search
    # near the top of a half-Moore window and widen downward only when stuck.
    Vmax = lib._moore_bound(d, D)
    top = min(Vmax, Vmax // 2 + 12)
    floor = max(best_n + 1, int(WINDOW_FRAC * top))
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = max(floor, best_n + 1)
        if lo > top:
            break
        cands = _candidates(d, lo, top)
        if not cands:
            floor = lo - 2
            continue
        rng.shuffle(cands)
        success = False
        for p, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            M = _size_matrix(p, d, rng)
            if M is None:
                continue
            res = _attempt(N, p, M, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            n, e = _graph(N, p, T, S)
            consider(n, e)
            success = True
            break
        if success:
            continue
        if budget < BUDGET_CAP:
            budget = min(BUDGET_CAP, budget * 1.5)
        elif floor > d + 1:
            floor -= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
