import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 24   # groups tried per (shape, order) attempt
ITERS = 900                   # annealing steps per group try
BUDGET0 = 3.0                 # initial seconds per attempt
BUDGET_CAP = 20.0             # maximum seconds per attempt


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x| Z_k of order N, coded as a*k + b.
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


# ----------------------------------------------------------------------------
# Multi-orbit bi-lift search.
#
# Base graph: a "A" vertices and b "B" vertices, with a count matrix C[i][j]
# giving the number of darts from A_i to B_j. Each dart (i, j, g) produces the
# perfect matching A_i x -- B_j (x*g) for all x in G. The lift has (a+b)*N
# vertices. Every A vertex has degree sum_j C[i][j] and every B vertex has
# degree sum_i C[i][j]; with row and column sums equal to d the lift is
# d-regular. Left multiplication is an automorphism, so the diameter is decided
# by eccentricities from the a+b orbit representatives (A_i, e) and (B_j, e).
#
# New shapes beyond the parent's bi-Cayley (a = b = 1) are the 2 x 2 bases
# [[p, d-p], [d-p, p]], which give 4N vertices with a different voltage space.
# ----------------------------------------------------------------------------

def _cost(N, a, b, darts, Tcol, V, D):
    """Total number of (orbit representative, vertex) pairs farther than D apart."""
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        col = Tcol[g]
        ai = i * N
        bj = (a + j) * N
        for x in range(N):
            y = bj + col[x]
            adj[ai + x].append(y)
            adj[y].append(ai + x)
    total = 0
    sources = [i * N for i in range(a)] + [(a + j) * N for j in range(b)]
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        count = 1
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
        total += V - count
    return total


def _anneal(N, a, b, C, Tcol, V, D, rng, iters, deadline):
    """Simulated annealing over voltages with fixed counts C; returns darts or None."""
    darts = []
    for i in range(a):
        for j in range(b):
            for g in rng.sample(range(N), C[i][j]):
                darts.append([i, j, g])
    if not darts:
        return None
    cur = _cost(N, a, b, darts, Tcol, V, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 3.0 * (1.0 - it / iters))
        k = rng.randrange(len(darts))
        i, j, old = darts[k]
        g = rng.randrange(N)
        if any(q[0] == i and q[1] == j and q[2] == g for q in darts):
            continue
        darts[k][2] = g
        v = _cost(N, a, b, darts, Tcol, V, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k][2] = old
    return darts if cur == 0 else None


def _attempt(N, a, b, C, D, rng, deadline):
    """Try groups of order N until one gives a valid voltage assignment."""
    groups = _groups(N)
    rng.shuffle(groups)
    V = (a + b) * N
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        Tcol = [[mul(x, g) for x in range(N)] for g in range(N)]
        darts = _anneal(N, a, b, C, Tcol, V, D, rng, ITERS, deadline)
        if darts is not None:
            return mul, darts
    return None


def _edges(N, a, b, darts, mul):
    """Expand darts into the explicit lifted graph."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, (a + j) * N + mul(x, g)))
    return (a + b) * N, edges


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

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

    if d >= 2 and D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    if d < 2 or D < 2:
        return best

    # Shapes: the bi-Cayley base (1,1), and 2x2 bases with row and column sums d.
    Mb = lib._moore_bound(d, D)
    shapes = [(1, 1, [[d]])]
    for p in range(1, d // 2 + 1):
        shapes.append((2, 2, [[p, d - p], [d - p, p]]))

    cfgs = []
    for a, b, C in shapes:
        guess = max(d + 1, Mb // (a + b) // 2)
        cfgs.append({
            "a": a, "b": b, "C": C,
            "N": guess, "lo": 0, "hi": None,
            "budget": BUDGET0,
        })

    while time.monotonic() < deadline:
        for cfg in cfgs:
            if time.monotonic() >= deadline:
                break
            a, b, C = cfg["a"], cfg["b"], cfg["C"]
            N = cfg["N"]
            att_deadline = min(deadline, time.monotonic() + cfg["budget"])
            res = _attempt(N, a, b, C, D, rng, att_deadline)
            lo, hi = cfg["lo"], cfg["hi"]
            if res is None:
                # Failure at N: lower the target, or bisect toward the last success.
                hi = N if hi is None else min(hi, N)
                cfg["hi"] = hi
                if lo == 0:
                    cfg["N"] = max(d + 1, N - max(1, N // 8))
                elif hi - lo > 1:
                    cfg["N"] = (lo + hi) // 2
                else:
                    cfg["N"] = hi
                    cfg["budget"] = min(BUDGET_CAP, cfg["budget"] * 1.5)
            else:
                # Success at N: record it and push the target up.
                mul, darts = res
                n, e = _edges(N, a, b, darts, mul)
                consider(n, e)
                lo = max(lo, N)
                cfg["lo"] = lo
                if hi is None:
                    cfg["N"] = lo + max(1, lo // 40)
                elif hi - lo > 1:
                    cfg["N"] = (lo + hi) // 2
                else:
                    cfg["N"] = hi
                    cfg["budget"] = min(BUDGET_CAP, cfg["budget"] * 1.5)

    return best
