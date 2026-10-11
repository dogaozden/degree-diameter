import itertools
import math
import random
import time

import lib

ITERS = 1500          # annealing steps per attempt
NMAX = 400            # largest group order used for a lift
BMAX = 8              # largest base size (vertices per side)
WINDOW = 4            # number of consecutive target orders tried per round
DUP_PENALTY = 40      # cost of a repeated (base-edge, voltage) dart
KNOWN_START = {(5, 5): 336}  # start the ladder at the known record as a safe fallback

_TCACHE = {}


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
# Base-graph lifts over finite groups.
#
# Base: b vertices per side (A_0..A_{b-1}, B_0..B_{b-1}). The base is d-regular
# bipartite: for each k in range(d), dart k joins A_i to B_{perm_k(i)} with a
# voltage volts[k][i] in G. The lift has vertices A(i,x), B(j,y), x,y in G, and
# A(i,x) ~ B(j, x*g) for every dart (i, j, g).
#
# Left multiplication by h is an automorphism, so eccentricities only need
# sources A(i,e) and B(j,e), i, j < b. This gives 2b sources.
# Vertex count 2*b*N, with N = |G|.
# ----------------------------------------------------------------------------

def _group_list(N):
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


def _tables(m, k, r):
    """Multiplication table T[x][g] = x*g for the group, cached."""
    key = (m, k, r)
    if key not in _TCACHE:
        order, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        _TCACHE[key] = (order, T)
    return _TCACHE[key]


def _score(b, N, T, d, D, perms, volts):
    """Return (cost, unreached) for the lift. cost = 0 iff the lift has diameter <= D and no duplicate darts."""
    VA = b * N
    V = 2 * VA
    nb = [[] for _ in range(V)]
    dup = 0
    for i in range(b):
        seen = set()
        base = i * N
        for k in range(d):
            j = perms[k][i]
            g = volts[k][i]
            if (j, g) in seen:
                dup += 1
            else:
                seen.add((j, g))
            off = VA + j * N
            for x in range(N):
                a = base + x
                y = off + T[x][g]
                nb[a].append(y)
                nb[y].append(a)

    reach = [0] * V
    for i in range(b):
        reach[i * N] |= 1 << i
    for j in range(b):
        reach[VA + j * N] |= 1 << (b + j)

    for _ in range(D):
        new = reach[:]
        changed = False
        for v in range(V):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            if r != reach[v]:
                new[v] = r
                changed = True
        reach = new
        if not changed:
            break

    unreached = sum(2 * b - r.bit_count() for r in reach)
    return unreached + DUP_PENALTY * dup, unreached


def _anneal(b, N, T, d, D, rng, deadline):
    """Simulated annealing over the dart permutations and voltages. Returns (perms, volts) or None."""
    perms = [rng.sample(range(b), b) for _ in range(d)]
    volts = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
    cur, _ = _score(b, N, T, d, D, perms, volts)
    for it in range(ITERS):
        if cur == 0:
            return perms, volts
        if it % 16 == 0 and time.monotonic() > deadline:
            return None
        temp = max(0.05, 2.0 * (1.0 - it / ITERS))
        if b > 1 and rng.random() < 0.08:
            k = rng.randrange(d)
            cand_perms = perms[:]
            cand_perms[k] = rng.sample(range(b), b)
            cand_volts = volts
        else:
            k = rng.randrange(d)
            i = rng.randrange(b)
            g = rng.randrange(N)
            cand_perms = perms
            cand_volts = [row[:] for row in volts]
            cand_volts[k][i] = g
        v, _ = _score(b, N, T, d, D, cand_perms, cand_volts)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            perms, volts, cur = cand_perms, cand_volts, v
    if cur == 0:
        return perms, volts
    return None


def _edges(b, N, T, d, perms, volts):
    """Build the (n, edges) lift from a successful configuration."""
    VA = b * N
    edges = []
    for k in range(d):
        for i in range(b):
            j = perms[k][i]
            g = volts[k][i]
            for x in range(N):
                edges.append((i * N + x, VA + j * N + T[x][g]))
    return 2 * VA, edges


def _tasks(V, d):
    """All (b, N, m, k, r) lift configurations with 2*b*N = V."""
    tasks = []
    for b in range(1, BMAX + 1):
        if V % (2 * b):
            continue
        N = V // (2 * b)
        if N < d or N > NMAX:
            continue
        for (m, k, r) in _group_list(N):
            tasks.append((b, N, m, k, r))
    return tasks


def _sweep(tasks, d, D, rng, t_end):
    """Round-robin annealing over the given tasks until t_end. Returns (n, edges) on success."""
    if not tasks:
        return None
    order_tasks = tasks[:]
    rng.shuffle(order_tasks)
    idx = 0
    while time.monotonic() < t_end:
        b, N, m, k, r = order_tasks[idx % len(order_tasks)]
        idx += 1
        _, T = _tables(m, k, r)
        res = _anneal(b, N, T, d, D, rng, t_end)
        if res is not None:
            perms, volts = res
            n, e = _edges(b, N, T, d, perms, volts)
            if lib.is_valid(n, e, d, D):
                return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Lift search: ladder of target orders V = 2*b*N, all above the current best.
    Vmoore = lib._moore_bound(d, D)
    lo = KNOWN_START.get((d, D), best[0] + 2)
    if lo % 2:
        lo += 1
    slice_t = 2.0

    while time.monotonic() < deadline and lo <= Vmoore:
        window = []
        for V in range(lo, lo + 2 * WINDOW, 2):
            if V > Vmoore:
                break
            tasks = _tasks(V, d)
            if tasks:
                window.append((V, tasks))
        if not window:
            lo += 2
            continue

        improved = False
        for V, tasks in window:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _sweep(tasks, d, D, rng, min(deadline, now + slice_t))
            if res is not None:
                consider(*res)
                lo = V + 2
                improved = True
                break
        if not improved:
            slice_t *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
