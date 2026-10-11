import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Search parameters for the voltage-lift search.
# ----------------------------------------------------------------------------
T_HOT = 2.0            # initial annealing temperature (unreached pairs)
T_COLD = 0.2           # final annealing temperature
ITERS = 500            # annealing steps per (group, base graph) try
GROUPS_PER_ATTEMPT = 4 # groups tried per (p, N) attempt
ATTEMPT_SECONDS = 2.0  # wall-clock cap per attempt
MAX_P = 6              # max base vertices per side in the lift
TIME_FRACTION = 0.8    # use this fraction of time_limit
TIME_SLACK = 1.5       # seconds kept in reserve


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid before use).
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
# Voltage lifts of small bipartite base graphs over groups of order N.
#
# Base: p "A" vertices and p "B" vertices, d darts per A vertex (d random
# permutations, so every B vertex also has d darts). A dart (i, j, g) with
# voltage g in G gives edges A_{i,x} -- B_{j, x*g} for all x in G.
# Left multiplication by h is an automorphism (A_{i,x} -> A_{i,hx}), so the
# diameter is exact once we check eccentricities from A_{i,e} and B_{j,e}.
# Lift order is n = 2*p*N. This generalizes the single-pair bi-Cayley search.
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


def _cost(p, N, D, T, invs, darts):
    """Count (source, vertex) pairs not within distance D, over the 2p fiber sources."""
    base = p * N
    tot = 2 * base
    outs = [[] for _ in range(p)]
    ins = [[] for _ in range(p)]
    for i, j, g in darts:
        outs[i].append((j, g))
        ins[j].append((i, invs[g]))
    sources = [i * N for i in range(p)] + [base + j * N for j in range(p)]
    total = 0
    for s in sources:
        seen = bytearray(tot)
        seen[s] = 1
        frontier = [s]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = base + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base, N)
                    row = T[y]
                    for i, h in ins[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += tot - count
    return total


def _anneal(p, N, D, T, invs, darts, rng, iters, deadline):
    """Simulated annealing over dart voltages to reach zero unreached pairs."""
    cur = _cost(p, N, D, T, invs, darts)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        new = rng.randrange(N)
        if new == old:
            continue
        darts[idx][2] = new
        v = _cost(p, N, D, T, invs, darts)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[idx][2] = old
    return cur == 0


def _attempt(p, N, d, D, rng, deadline):
    """Try a few groups of order N with a random base graph on p + p vertices."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        darts = []
        for _ in range(d):
            perm = list(range(p))
            rng.shuffle(perm)
            for i in range(p):
                darts.append([i, perm[i], rng.randrange(N)])
        if _anneal(p, N, D, T, invs, darts, rng, ITERS, deadline):
            return p, N, T, darts
    return None


def _lift(p, N, T, darts):
    """Expand the voltage lift into (n, edges) with a deduplicated edge set."""
    base = p * N
    edges = set()
    for i, j, g in darts:
        for x in range(N):
            edges.add((i * N + x, base + j * N + T[x][g]))
    return 2 * base, sorted(edges)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, TIME_FRACTION * time_limit - TIME_SLACK)
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

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if d < 2:
        return best

    # Cheap fallbacks: K_{d,d} (diameter 2), PG(2,q) (diameter 3), W(q) (diameter 4).
    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift search with randomized base graphs and groups.
    Moore = lib._moore_bound(d, D)
    window = 12
    fails = 0
    while time.monotonic() < deadline:
        lo = best_n + 1
        hi = min(Moore, best_n + window)
        if lo > hi:
            break
        cands = []
        for p in range(1, MAX_P + 1):
            n_min = max(2, (lo + 2 * p - 1) // (2 * p))
            n_max = hi // (2 * p)
            for N in range(n_min, n_max + 1):
                cands.append((p, N))
        if not cands:
            if hi >= Moore:
                break
            window += 12
            continue
        p, N = rng.choice(cands)
        att_deadline = min(deadline, time.monotonic() + ATTEMPT_SECONDS)
        res = _attempt(p, N, d, D, rng, att_deadline)
        if res is not None:
            p, N, T, darts = res
            n, e = _lift(p, N, T, darts)
            consider(n, e)
            fails = 0
        else:
            fails += 1
            if fails % 30 == 0:
                window += 12

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
