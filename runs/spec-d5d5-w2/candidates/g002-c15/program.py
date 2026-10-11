import itertools
import math
import random
import time

import lib

MAX_GROUPS = 6        # groups tried per (k, N) attempt
ITERS = 900           # annealing steps per group
T_HOT = 1.5           # initial annealing temperature (unreached-pair units)
T_COLD = 0.15         # final annealing temperature
BASE_BUDGET = 1.5     # seconds for the first attempt of a failure streak
MAX_BUDGET = 10.0     # cap on per-attempt seconds
K_CHOICES = (1, 2, 2, 3, 3, 4)   # base-graph sizes per side (k=1 is bi-Cayley)


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
# Voltage lifts of a small bipartite base graph over a non-cyclic group.
#
# Base: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, with a k x k
# matrix M of nonnegative integers whose row and column sums are all d.
# Each base dart (i, j) carries a voltage g in G (|G| = N). Lift vertices are
# A_{i,x} and B_{j,y} for x, y in G; dart (i,j,g) joins A_{i,x} -- B_{j,x g}.
# Left multiplication by h is an automorphism, so eccentricities inside each
# fibre are equal and only the 2k representatives A_{i,e}, B_{j,e} must be checked.
# Lift order: 2kN. For k = 1 this is the bi-Cayley search.
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


def _random_base(k, d, rng):
    """Random k x k nonnegative integer matrix with all row and column sums d (sum of d permutations)."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            M[i][p[i]] += 1
    return M


def _lift_cost(k, N, D, T, invs, darts, volts):
    """Total number of (source, vertex) pairs not within distance D, over the 2k fibre representatives."""
    V = k * N
    out = [[] for _ in range(k)]
    inn = [[] for _ in range(k)]
    for t, (i, j) in enumerate(darts):
        g = volts[t]
        out[i].append((j, g))
        inn[j].append((i, invs[g]))
    sources = [i * N for i in range(k)] + [V + j * N for j in range(k)]
    total = 0
    for s in sources:
        seen = bytearray(2 * V)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < V:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = V + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - V, N)
                    row = T[y]
                    for i, h in inn[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += 2 * V - count
    return total


def _lift_edges(k, N, T, darts, volts):
    """Edges of the voltage lift: dart (i, j, g) joins A_{i,x} to B_{j, x g} for every x."""
    V = k * N
    edges = []
    for t, (i, j) in enumerate(darts):
        g = volts[t]
        for x in range(N):
            edges.append((i * N + x, V + j * N + T[x][g]))
    return edges


def _try_lift(k, N, d, D, deadline, rng):
    """Search voltages on a k-vertex-per-side base over groups of order N. Return (n, edges) or None."""
    groups = _groups(N)
    if not groups:
        return None
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        M = _random_base(k, d, rng)
        if max(max(row) for row in M) > N:
            continue   # not enough distinct voltages for parallel darts
        darts = []
        for i in range(k):
            for j in range(k):
                darts += [(i, j)] * M[i][j]
        cells = {}
        for t, key in enumerate(darts):
            cells.setdefault(key, []).append(t)
        volts = [0] * len(darts)
        for ts in cells.values():
            for t, g in zip(ts, rng.sample(range(N), len(ts))):
                volts[t] = g
        cur = _lift_cost(k, N, D, T, invs, darts, volts)
        for it in range(ITERS):
            if cur == 0 or time.monotonic() > deadline:
                break
            temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
            t = rng.randrange(len(darts))
            key = darts[t]
            g = rng.randrange(N)
            if any(volts[s] == g for s in cells[key]):
                continue
            old = volts[t]
            volts[t] = g
            v = _lift_cost(k, N, D, T, invs, darts, volts)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volts[t] = old
        if cur == 0:
            return 2 * k * N, _lift_edges(k, N, T, darts, volts)
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
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    caps = {}          # per-k top of the search window, lowered on failures
    fails = 0

    while time.monotonic() < deadline:
        options = []
        for k in set(K_CHOICES):
            Nmax = moore // (2 * k)
            cap = caps.get(k, Nmax)
            lo = max(2, best_n // (2 * k) + 1)
            if 2 <= lo <= cap:
                options.append((k, lo, cap))
        if not options:
            break
        k, lo, cap = rng.choice(options)
        N = rng.randint(max(lo, cap - 6), cap)

        now = time.monotonic()
        budget = min(MAX_BUDGET, BASE_BUDGET * (1.3 ** min(fails, 12)))
        att_deadline = min(deadline, now + budget)
        res = _try_lift(k, N, d, D, att_deadline, rng)
        if res is not None:
            consider(res[0], res[1])
            fails = 0
        else:
            fails += 1
            if N == cap:
                caps[k] = cap - 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
