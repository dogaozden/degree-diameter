import itertools
import math
import random
import time

import lib

ITERS = 3000          # annealing steps per lift attempt
ATTEMPT_BUDGET = 3.0  # seconds per lift attempt
PERM_MOVE_P = 0.15    # probability of a permutation-layer move (base sizes b > 1)


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
# Voltage lifts over base graphs with b vertices per side.
#
# Base: A_0..A_{b-1}, B_0..B_{b-1}. The base multigraph is the union of d
# permutation layers: layer l contributes darts A_i -- B_{perm_l[i]}. Each dart
# carries a voltage g in a finite group G of order M. The lift has vertices
# (class, x) for x in G, and dart (i, j, g) joins (A_i, x) to (B_j, x*g).
#
# Left translation by G is an automorphism, so each base class is vertex
# transitive and the diameter is certified by BFS from the 2b class
# representatives (class, identity). b = 1 is the bi-Cayley family.
# ----------------------------------------------------------------------------

def _groups(M):
    """Return semidirect parameters (m, k, r) with m*k = M, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(M, m, k, r):
    """Multiplication table T[x][g] = x*g and inverse list I[g] for the group Z_m x|_r Z_k."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(M)] for x in range(M)]
    I = [inv(g) for g in range(M)]
    return T, I


def _cost(b, M, T, I, layers, vol, D):
    """Total unreached (source, vertex) pairs over the 2b class representatives."""
    outA = [[] for _ in range(b)]
    inB = [[] for _ in range(b)]
    t = 0
    for perm in layers:
        for i in range(b):
            j = perm[i]
            g = vol[t]
            t += 1
            outA[i].append((b + j, g))
            inB[j].append((i, I[g]))
    N = 2 * b * M
    total = 0
    for c0 in range(2 * b):
        seen = bytearray(N)
        src = c0 * M
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                c, x = divmod(u, M)
                row = T[x]
                if c < b:
                    for tc, g in outA[c]:
                        v = tc * M + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for tc, gi in inB[c - b]:
                        v = tc * M + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _lift_edges(b, M, T, layers, vol):
    """Explicit edge list of the lift (duplicates removed), with n = 2*b*M vertices."""
    E = set()
    t = 0
    for perm in layers:
        for i in range(b):
            j = perm[i]
            g = vol[t]
            t += 1
            for x in range(M):
                E.add((i * M + x, (b + j) * M + T[x][g]))
    return 2 * b * M, sorted(E)


def _anneal(b, M, T, I, d, D, rng, iters, deadline):
    """Simulated annealing over permutation layers and voltages to zero unreached pairs."""
    layers = [rng.sample(range(b), b) for _ in range(d)]
    vol = [rng.randrange(M) for _ in range(d * b)]
    cur = _cost(b, M, T, I, layers, vol, D)
    t0 = 1.0 + 0.05 * cur
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.2, t0 * (1.0 - it / iters))
        if b > 1 and rng.random() < PERM_MOVE_P:
            l = rng.randrange(d)
            old = layers[l]
            layers[l] = rng.sample(range(b), b)
            v = _cost(b, M, T, I, layers, vol, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                layers[l] = old
        else:
            t = rng.randrange(d * b)
            old = vol[t]
            vol[t] = rng.randrange(M)
            v = _cost(b, M, T, I, layers, vol, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                vol[t] = old
    return (layers, vol) if cur == 0 else None


# ----------------------------------------------------------------------------
# Top level.
# ----------------------------------------------------------------------------

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

    if D == 1:
        consider(2, [(0, 1)])
        return best if lib.is_valid(best[0], best[1], d, D) else (1, [])
    if d == 1:
        consider(2, [(0, 1)])
        return best if lib.is_valid(best[0], best[1], d, D) else (1, [])
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best if lib.is_valid(best[0], best[1], d, D) else (1, [])

    # Safe baseline: K_{d,d} has diameter 2.
    consider(*lib.haar_graph(d, range(d)))

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best if lib.is_valid(best[0], best[1], d, D) else (1, [])
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift search with base sizes b = 1..4.
    Moore = lib._moore_bound(d, D)
    bs = [1, 2, 3, 4]
    while time.monotonic() < deadline and bs:
        b = rng.choice(bs)
        Mmin = best[0] // (2 * b) + 1
        Mmax = Moore // (2 * b)
        if Mmin > Mmax:
            bs.remove(b)
            continue
        M = Mmin + rng.randrange(0, 3)
        if M > Mmax:
            M = Mmin
        groups = _groups(M)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        T, I = _tables(M, m, k, r)
        now = time.monotonic()
        att_deadline = min(deadline, now + ATTEMPT_BUDGET)
        res = _anneal(b, M, T, I, d, D, rng, ITERS, att_deadline)
        if res is None:
            continue
        layers, vol = res
        n, e = _lift_edges(b, M, T, layers, vol)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
