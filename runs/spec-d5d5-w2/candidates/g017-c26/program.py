import itertools
import math
import random
import time

import lib

WEIGHT_DUP = 50      # penalty per duplicate dart (parallel edge) in a lift
T_HOT = 2.0          # annealing start temperature (unreached-pair units)
T_COLD = 0.2         # annealing end temperature
MAX_A = 6            # max base-graph vertices per side
STEPS = 250          # annealing steps per (N, group) attempt
GROUPS_PER_N = 4     # groups tried per (a, N) before moving on


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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: voltage lifts over small multi-vertex bipartite base graphs.
#
# Base: a vertices on side A and a on side B, joined by d "layers". Layer k is a
# permutation sig[k] of range(a) (so every base vertex has degree d) with a
# voltage volt[k][i] in a finite group G of order N. The lift has 2*a*N
# vertices: A-vertex (i, x) joins B-vertex (sig[k][i], x * volt[k][i]).
# Left multiplication by G is an automorphism, so the diameter is decided by
# BFS from the identity fiber of each base vertex (2a sources).
# a = 1 recovers bi-Cayley graphs; a >= 2 gives richer base structure.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(order)] for x in range(order)]


def _lift_adj(a, N, d, M, sig, volt):
    """Adjacency of the lift and the number of duplicate darts (parallel edges)."""
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    seen = set()
    dups = 0
    aN = a * N
    for k in range(d):
        sk = sig[k]
        vk = volt[k]
        for i in range(a):
            j = sk[i]
            g = vk[i]
            key = (i, j, g)
            if key in seen:
                dups += 1
            else:
                seen.add(key)
            base_a = i * N
            base_b = aN + j * N
            for x in range(N):
                u = base_a + x
                v = base_b + M[x][g]
                adj[u].append(v)
                adj[v].append(u)
    return adj, dups


def _within(adj, src, V, D):
    """Number of vertices within distance D of src."""
    seen = bytearray(V)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _cost(a, N, d, D, M, sig, volt):
    adj, dups = _lift_adj(a, N, d, M, sig, volt)
    V = 2 * a * N
    unreached = 0
    for u in range(2 * a):          # identity fiber of each base vertex
        unreached += V - _within(adj, u * N, V, D)
    return unreached + WEIGHT_DUP * dups


def _anneal(a, N, d, D, M, rng, steps, deadline):
    """Anneal permutations and voltages until the lift has diameter <= D and no parallel darts."""
    sig = []
    volt = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        sig.append(p)
        volt.append([rng.randrange(N) for _ in range(a)])
    cur = _cost(a, N, d, D, M, sig, volt)
    for it in range(steps):
        if cur == 0:
            return sig, volt
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / steps)
        k = rng.randrange(d)
        if a > 1 and rng.random() < 0.4:
            i1, i2 = rng.sample(range(a), 2)
            sk = sig[k]
            sk[i1], sk[i2] = sk[i2], sk[i1]
            new = _cost(a, N, d, D, M, sig, volt)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                sk[i1], sk[i2] = sk[i2], sk[i1]
        else:
            i = rng.randrange(a)
            old = volt[k][i]
            volt[k][i] = rng.randrange(N)
            new = _cost(a, N, d, D, M, sig, volt)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                volt[k][i] = old
    if cur == 0:
        return sig, volt
    return None


def _lift_edges(a, N, d, M, sig, volt):
    aN = a * N
    edges = []
    for k in range(d):
        for i in range(a):
            j = sig[k][i]
            g = volt[k][i]
            for x in range(N):
                edges.append((i * N + x, aN + j * N + M[x][g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 3.0)
    deadline = start + max(0.3, budget)
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

    moore = lib.moore_bound(d, D)

    # Voltage-lift search over multi-vertex base graphs and many groups.
    while time.monotonic() < deadline:
        feas = [a for a in range(1, MAX_A + 1)
                if best[0] // (2 * a) + 1 <= moore // (2 * a)]
        if not feas:
            break
        a = rng.choice(feas)
        lo = best[0] // (2 * a) + 1
        Nmax = moore // (2 * a)
        N = rng.randint(lo, min(Nmax, lo + 3))
        groups = _groups(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:GROUPS_PER_N]:
            if time.monotonic() >= deadline:
                break
            M = _mul_table(m, k, r)
            res = _anneal(a, N, d, D, M, rng, STEPS, deadline)
            if res is not None:
                sig, volt = res
                consider(2 * a * N, _lift_edges(a, N, d, M, sig, volt))
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
