import math
import random
import time

import lib

T_HOT = 1.5         # initial annealing temperature (unreached-pair units)
T_COLD = 0.1        # final annealing temperature
ITERS = 4000        # annealing steps per (base, group) try
ATTEMPT_CAP = 6.0   # seconds per attempted group order N
GROUPS_PER_N = 6    # groups tried per order N


# ----------------------------------------------------------------------------
# Baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over finite groups.
#
# Base graph: k vertices on side A (0..k-1) and k on side B. The base multigraph
# is d-regular and bipartite, with c[u][v] parallel darts between u and v. Each
# dart carries a group voltage g. The lift has 2k*N vertices (u, x), x in G,
# with edges (u, x) -- (v, x*g). Parallel darts between the same base pair use
# distinct voltages, so the lift is simple and exactly d-regular.
#
# Left multiplication by h is an automorphism of the lift, so only the 2k
# identity lifts (base u, x = e) need to be used as BFS sources.
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


def _random_base(k, d, rng):
    """Random d-regular bipartite multigraph on k + k base vertices, as a k x k count matrix."""
    A = [u for u in range(k) for _ in range(d)]
    B = [v for v in range(k) for _ in range(d)]
    rng.shuffle(B)
    c = [[0] * k for _ in range(k)]
    for u, v in zip(A, B):
        c[u][v] += 1
    return c


def _initial_darts(c, N, rng):
    """Assign distinct random voltages to the darts of each base pair."""
    k = len(c)
    darts = []
    used = {}
    for u in range(k):
        for v in range(k):
            vals = rng.sample(range(N), c[u][v])
            used[(u, v)] = set(vals)
            for g in vals:
                darts.append([u, v, g])
    return darts, used


def _unreached(darts, k, N, T, invs, D):
    """Count (source, vertex) pairs not within distance D, over the 2k identity sources."""
    nb = [[] for _ in range(2 * k)]
    for u, v, g in darts:
        nb[u].append((k + v, g))         # (u, x) -> (v, x*g)
        nb[k + v].append((u, invs[g]))   # (v, y) -> (u, y*g^-1)
    V = 2 * k * N
    total = 0
    for src in range(2 * k):
        seen = bytearray(V)
        s = src * N                      # identity element has index 0
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                b, x = divmod(w, N)
                row = T[x]
                for ob, gg in nb[b]:
                    y = ob * N + row[gg]
                    if not seen[y]:
                        seen[y] = 1
                        nxt.append(y)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(k, d, N, T, invs, D, rng, deadline, iters):
    """Anneal dart voltages (on a random base) until every pair is within distance D."""
    c = _random_base(k, d, rng)
    darts, used = _initial_darts(c, N, rng)
    cur = _unreached(darts, k, N, T, invs, D)
    n_darts = len(darts)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(n_darts)
        u, v, old = darts[i]
        new = rng.randrange(N)
        if new in used[(u, v)]:
            continue
        darts[i][2] = new
        val = _unreached(darts, k, N, T, invs, D)
        if val <= cur or rng.random() < math.exp(-(val - cur) / temp):
            used[(u, v)].discard(old)
            used[(u, v)].add(new)
            cur = val
        else:
            darts[i][2] = old
    if cur == 0:
        return darts
    return None


def _attempt(k, d, N, D, rng, deadline):
    """Try groups of order N for a k-vertex-per-side base; return (darts, mul) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:GROUPS_PER_N]:
        now = time.monotonic()
        if now > deadline:
            return None
        group_deadline = min(deadline, now + max(0.5, (deadline - now) / 3))
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = _anneal(k, d, N, T, invs, D, rng, group_deadline, ITERS)
        if darts is not None:
            return darts, mul
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

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    mb = lib._moore_bound(d, D)

    while time.monotonic() < deadline:
        options = []
        for k in (2, 3):
            hi = mb // (2 * k)
            lo = max(d + 1, best_n // (2 * k) + 1)
            if lo <= hi:
                options.append(k)
        if not options:
            break
        k = rng.choice(options)
        hi = mb // (2 * k)
        lo = max(d + 1, best_n // (2 * k) + 1)
        N = rng.randint(lo, min(hi, lo + 4))

        att_deadline = min(deadline, time.monotonic() + ATTEMPT_CAP)
        res = _attempt(k, d, N, D, rng, att_deadline)
        if res is None:
            continue
        darts, mul = res
        base_darts = [(u, k + v, g) for u, v, g in darts]
        n, e = lib.group_lift(2 * k, base_darts, N, mul)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
