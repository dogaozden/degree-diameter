import math
import random
import time

import lib

MAX_GROUPS = 6            # groups tried per (b, N) attempt
ITERS = 700               # annealing steps per group
T_HOT = 1.2               # initial annealing temperature (unreached-pair units)
T_COLD = 0.1              # final annealing temperature
WINDOW_FRAC = 0.97        # search total sizes in [WINDOW_FRAC * top, top] first
BUDGET_START = 2.5        # seconds per attempt at the start
BUDGET_CAP = 8.0          # cap on seconds per attempt as failures pile up
B_CHOICES = (1, 1, 2, 2, 3, 4)  # base-graph sizes per side; b > 1 is the non-bi-Cayley family


# ----------------------------------------------------------------------------
# Baseline family (fast, always validated).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base graphs over finite groups.
#
# Base: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}, with a d-regular
# bipartite multigraph of b*d darts (i, j, g). Dart (i, j, g) joins
# (A_i, x) to (B_j, x*g) for every x in G. The lift has 2*b*|G| vertices,
# is bipartite, and has degree exactly d. Left multiplication by h is an
# automorphism, so it suffices to BFS from (A_i, e) and (B_j, e).
#
# Vertex ids: A_i, x -> i*N + x ; B_j, y -> b*N + j*N + y.
# Parallel darts (same i, j) must carry distinct voltages.
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


def _random_base(b, d, rng):
    """Darts of a d-regular bipartite multigraph on b+b vertices: union of d random permutations."""
    darts = []
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        for i in range(b):
            darts.append((i, p[i]))
    return darts


def _unreached(adj, n, b, N, D):
    """Count (source, vertex) pairs not within distance D, over the 2b base sources."""
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(n)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _anneal(N, b, D, darts, mt, rng, deadline):
    """Simulated annealing over dart voltages to zero the number of unreached pairs."""
    n = 2 * b * N
    L = len(darts)
    same = [[s for s in range(L) if s != t and darts[s] == darts[t]] for t in range(L)]

    def cost(volt):
        adj = [[] for _ in range(n)]
        for t, (i, j) in enumerate(darts):
            g = volt[t]
            bj = b * N + j * N
            for x in range(N):
                a = i * N + x
                c = bj + mt[x][g]
                adj[a].append(c)
                adj[c].append(a)
        return _unreached(adj, n, b, N, D)

    def conflict(volt, t, g):
        return any(volt[s] == g for s in same[t])

    # Initial voltages, respecting the distinct-voltage rule for parallel darts.
    volt = []
    for t in range(L):
        opts = [g for g in range(N) if not any(volt[s] == g for s in same[t] if s < t)]
        if not opts:
            return None
        volt.append(rng.choice(opts))

    cur = cost(volt)
    for it in range(ITERS):
        if cur == 0:
            return volt
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        t = rng.randrange(L)
        g = rng.randrange(N)
        if g == volt[t] or conflict(volt, t, g):
            continue
        old = volt[t]
        volt[t] = g
        v = cost(volt)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volt[t] = old
    return volt if cur == 0 else None


def _attempt(b, N, d, D, rng, deadline):
    """Try random groups of order N and a random base graph; return (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        mt = [[mul(x, g) for g in range(N)] for x in range(N)]
        darts = _random_base(b, d, rng)
        volt = _anneal(N, b, D, darts, mt, rng, deadline)
        if volt is not None:
            edges = []
            for t, (i, j) in enumerate(darts):
                g = volt[t]
                bj = b * N + j * N
                for x in range(N):
                    edges.append((i * N + x, bj + mt[x][g]))
            return 2 * b * N, edges
    return None


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

    if d < 2 or D < 2:
        return best

    cap = lib._moore_bound(d, D)
    fails = 0
    budget = BUDGET_START
    skips = 0

    while time.monotonic() < deadline:
        if best_n >= cap:
            break
        b = rng.choice(B_CHOICES)
        Ntop = cap // (2 * b)
        frac = max(0.6, WINDOW_FRAC - 0.01 * fails)
        lo = max(d + 1, best_n // (2 * b) + 1, int(frac * Ntop))
        if lo > Ntop:
            skips += 1
            if skips > 500:
                break
            continue
        skips = 0
        N = rng.randint(lo, Ntop)
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(b, N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            budget = min(BUDGET_CAP, budget + 0.5)
        else:
            n, e = res
            consider(n, e)
            fails = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
