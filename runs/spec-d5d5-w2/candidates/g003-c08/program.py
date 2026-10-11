import math
import random
import time

import lib

ITERS = 1200          # annealing steps per (group, dart assignment) try
T_HOT = 2.0           # initial temperature (unreached-pair units)
T_COLD = 0.2          # final temperature
MAX_GROUPS = 10       # groups tried per (K, N) attempt
GROUP_BUDGET = 3.0    # seconds per group try
SPAN = 10             # width of the N window above the lower floor
FLOOR_FRAC = 0.5      # aim for about FLOOR_FRAC * Moore-bound vertices


# ----------------------------------------------------------------------------
# Baseline families (always validated before being kept).
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
# Generalized voltage lift over a group of order N with K A-orbits and K B-orbits.
#
# Vertices: A-side (a, x) -> a*N + x, B-side (K+b, y) -> (K+b)*N + y.
# Each dart (a, b, g) gives edges (a, x) -- (b, x*g) for all x. Left
# multiplication by the group is an automorphism, so eccentricities need only
# be checked from the base vertices (a, e) and (K+b, e).
# Each cell (a, b) carries C[a][b] distinct darts, so every vertex has degree d
# when every row and column of C sums to d.
# ----------------------------------------------------------------------------

def _cost(K, N, T, darts, D):
    """Total number of (base source, vertex) pairs not within distance D."""
    KN = K * N
    adj = [[] for _ in range(2 * KN)]
    for a, b, g in darts:
        for x in range(N):
            u = a * N + x
            v = KN + b * N + T[x][g]
            adj[u].append(v)
            adj[v].append(u)
    total = 0
    sources = [a * N for a in range(K)] + [KN + b * N for b in range(K)]
    for s in sources:
        seen = bytearray(2 * KN)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += 2 * KN - count
    return total


def _random_counts(K, d, rng):
    """K x K nonnegative integer matrix with all row and column sums d (sum of d permutations)."""
    C = [[0] * K for _ in range(K)]
    for _ in range(d):
        perm = list(range(K))
        rng.shuffle(perm)
        for a in range(K):
            C[a][perm[a]] += 1
    return C


def _initial_darts(K, N, d, rng):
    C = _random_counts(K, d, rng)
    darts = []
    for a in range(K):
        for b in range(K):
            for g in rng.sample(range(N), C[a][b]):
                darts.append((a, b, g))
    return darts


def _anneal(K, N, T, darts, D, rng, iters, deadline):
    """Anneal dart group elements to zero out unreached pairs. Returns darts or None."""
    darts = list(darts)
    cur = _cost(K, N, T, darts, D)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(len(darts))
        a, b, g_old = darts[i]
        g_new = rng.randrange(N)
        if any(a2 == a and b2 == b and g2 == g_new for a2, b2, g2 in darts):
            continue
        darts[i] = (a, b, g_new)
        v = _cost(K, N, T, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[i] = (a, b, g_old)
    return darts if cur == 0 else None


def _edges(K, N, T, darts):
    edges = []
    for a, b, g in darts:
        for x in range(N):
            edges.append((a * N + x, (K + b) * N + T[x][g]))
    return edges


def _attempt(K, N, d, D, rng, deadline):
    """Try groups of order N for a K-orbit lift; return (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        now = time.monotonic()
        if now >= deadline:
            return None
        order, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts0 = _initial_darts(K, N, d, rng)
        darts = _anneal(K, N, T, darts0, D, rng, ITERS, min(deadline, now + GROUP_BUDGET))
        if darts is not None:
            return 2 * K * N, _edges(K, N, T, darts)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Always-valid fallback: K_{1,1} for D >= 1, K_{d,d} for D >= 2 (diameter 2).
    consider(2, [(0, 1)])
    if D == 1:
        return best
    if d >= 2:
        consider(2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if d == 2:
        n = 2 * D   # cycle of length 2D is optimal for degree 2
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3:
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except (ValueError, RuntimeError):
                pass

    if d < 3:
        return best

    # Generalized voltage lifts with K = 1, 2, 3 base orbits per side.
    M = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        opts = []
        for K in (1, 2, 3):
            hi_all = M // (2 * K)
            lo = max(d, best[0] // (2 * K) + 1, M // (4 * K))
            hi = min(hi_all, lo + SPAN)
            if lo <= hi:
                opts.append((K, lo, hi))
        if not opts:
            break
        K, lo, hi = rng.choice(opts)
        N = rng.randint(lo, hi)
        res = _attempt(K, N, d, D, rng, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
