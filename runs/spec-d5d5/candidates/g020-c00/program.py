import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 10   # groups tried per (p, N) attempt
ITERS = 4000                  # annealing steps per group try
BASE_SIZES = (2, 3, 4, 1)     # base vertices per side of the voltage lift


# ----------------------------------------------------------------------------
# Baseline families (always validated with lib.is_valid before use).
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
# Voltage lifts over non-cyclic groups with a small base graph.
#
# Base: p vertices A_0..A_{p-1} and p vertices B_0..B_{p-1}, d-regular bipartite
# multigraph built as d permutations sig[t] (A_i -- B_{sig[t][i]}), each dart
# carrying a voltage volt[t][i] in G = Z_m x| Z_k.
# Lift: A_i,x -- B_j, x*g. Left multiplication by G is an automorphism that
# fixes each fiber, so eccentricities come from the 2p identity vertices only.
# Total order 2*p*N.
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


def _unreached(p, N, D, T, adjA, adjB, src):
    """Count vertices not within distance D of the source vertex index src."""
    V = 2 * p * N
    boff = p * N
    seen = bytearray(V)
    seen[src] = 1
    count = 1
    frontier = [src]
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < boff:
                i, x = divmod(u, N)
                row = T[x]
                for j, g in adjA[i]:
                    v = boff + j * N + row[g]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                j, y = divmod(u - boff, N)
                row = T[y]
                for i, gi in adjB[j]:
                    v = i * N + row[gi]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        if not nxt:
            break
        frontier = nxt
    return V - count


def _cost(p, N, d, D, T, invs, sig, volt):
    """Total unreached pairs over the 2p fiber-identity sources."""
    adjA = [[] for _ in range(p)]
    adjB = [[] for _ in range(p)]
    for t in range(d):
        for i in range(p):
            j = sig[t][i]
            g = volt[t][i]
            adjA[i].append((j, g))
            adjB[j].append((i, invs[g]))
    boff = p * N
    sources = [i * N for i in range(p)] + [boff + j * N for j in range(p)]
    total = 0
    for src in sources:
        total += _unreached(p, N, D, T, adjA, adjB, src)
    return total


def _anneal_lift(p, N, d, D, T, invs, rng, iters, deadline):
    """Simulated annealing over voltages for a fixed random base graph."""
    sig = [rng.sample(range(p), p) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(p)] for _ in range(d)]
    cur = _cost(p, N, d, D, T, invs, sig, volt)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        t = rng.randrange(d)
        i = rng.randrange(p)
        old = volt[t][i]
        new = rng.randrange(N)
        if new == old:
            continue
        volt[t][i] = new
        v = _cost(p, N, d, D, T, invs, sig, volt)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            volt[t][i] = old
    if cur == 0:
        return sig, volt
    return None


def _attempt_lift(p, N, d, D, rng, deadline):
    """Try groups of order N for a p-vertex-per-side lift; return solution or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() >= deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        sol = _anneal_lift(p, N, d, D, T, invs, rng, ITERS, deadline)
        if sol is not None:
            return p, N, T, sol[0], sol[1]
    return None


def _edges(p, N, T, sig, volt, d):
    """Materialize the lift as an edge list on 2*p*N vertices."""
    boff = p * N
    E = set()
    for t in range(d):
        for i in range(p):
            j = sig[t][i]
            g = volt[t][i]
            for x in range(N):
                a = i * N + x
                b = boff + j * N + T[x][g]
                E.add((a, b) if a < b else (b, a))
    return sorted(E)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    # Safe baselines.
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

    # Main search: voltage lifts with small base graphs over non-cyclic groups.
    budget = 0.5
    while time.monotonic() < deadline:
        targets = []
        for p in BASE_SIZES:
            Nlo = best_n // (2 * p) + 1
            Nhi = moore // (2 * p)
            for N in range(Nlo, min(Nhi, Nlo + 2) + 1):
                targets.append((2 * p * N, p, N))
        if not targets:
            break
        targets.sort()
        found = False
        for V, p, N in targets:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt_lift(p, N, d, D, rng, min(deadline, now + budget))
            if res is not None:
                rp, rN, T, sig, volt = res
                consider(2 * rp * rN, _edges(rp, rN, T, sig, volt, d))
                found = True
                break
        if not found:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
