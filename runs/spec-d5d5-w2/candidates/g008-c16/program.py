import itertools
import math
import random
import time

import lib

ITERS = 700          # annealing steps per (k, N, group) attempt
MAX_GROUPS = 8       # groups tried per (k, N) choice
MAX_K = 6            # largest base-orbit count k per side
GROUP_SEC = 2.0      # wall-clock budget per group attempt
T_HOT = 6.0          # initial annealing temperature (unreached-pair units)
T_COLD = 0.3         # final annealing temperature


# ----------------------------------------------------------------------------
# Fallback families (cheap, validated before use).
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
    """W(q) for the largest prime power q with q + 1 <= d (small q only, for speed)."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-lift search.
#
# Base graph: k vertices A^0..A^{k-1} and k vertices B^0..B^{k-1}. The base
# multigraph is d-regular on each side, given by d permutations sig[t] of
# range(k): dart (i, t) joins A^i to B^{sig[t][i]} with voltage volt[i][t] in G.
# Lift: A^i_x -- B^{sig[t][i]}_{x * g}. Left multiplication by G is an
# automorphism, so the diameter is decided by BFS from the 2k sources
# A^i_e and B^j_e (identity element e = code 0).
# Vertex ids: A^i_x -> i*N + x ; B^j_y -> k*N + j*N + y.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (includes cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(k, N, d, D, T, invs, sig, volt):
    """Total number of (source, vertex) pairs not within distance D over all 2k orbit sources."""
    kN = k * N
    V = 2 * kN
    arcs = [[(sig[t][i], volt[i][t]) for t in range(d)] for i in range(k)]
    inc = [[] for _ in range(k)]
    for i in range(k):
        for j, g in arcs[i]:
            inc[j].append((i, invs[g]))
    total = 0
    for s in range(2 * k):
        src = s * N if s < k else kN + (s - k) * N
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    Tx = T[x]
                    for j, g in arcs[i]:
                        v = kN + j * N + Tx[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    Ty = T[y]
                    for i, gi in inc[j]:
                        v = i * N + Ty[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(k, N, d, D, T, invs, rng, deadline):
    """Anneal voltages and base permutations to zero unreached pairs; return (sig, volt) or None."""
    sig = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        sig.append(p)
    volt = [[rng.randrange(N) for _ in range(d)] for _ in range(k)]
    cur = _unreached(k, N, d, D, T, invs, sig, volt)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        if k == 1 or rng.random() < 0.75:
            # Change one voltage.
            i = rng.randrange(k)
            t = rng.randrange(d)
            old = volt[i][t]
            new = rng.randrange(N)
            if new == old:
                continue
            volt[i][t] = new
            v = _unreached(k, N, d, D, T, invs, sig, volt)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[i][t] = old
        else:
            # Swap two entries of one base permutation.
            t = rng.randrange(d)
            old = sig[t]
            new = old[:]
            a, b = rng.sample(range(k), 2)
            new[a], new[b] = new[b], new[a]
            sig[t] = new
            v = _unreached(k, N, d, D, T, invs, sig, volt)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                sig[t] = old
    if cur == 0:
        return sig, volt
    return None


def _lift_edges(k, N, d, T, sig, volt):
    """Edge list and order of the lift described by (sig, volt)."""
    kN = k * N
    E = set()
    for i in range(k):
        for t in range(d):
            j = sig[t][i]
            g = volt[i][t]
            for x in range(N):
                E.add((i * N + x, kN + j * N + T[x][g]))
    return 2 * kN, sorted(E)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching shortcut: incidence graph of PG(2, d-1).
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

    # Bipartite lift has 2*k*N vertices, so k*N is at most half the Moore bound.
    half = lib._moore_bound(d, D) // 2
    W = 4
    while time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > half:
            break
        hi = min(half, lo + W)
        X = rng.randint(lo, hi)
        ks = [k for k in range(1, MAX_K + 1) if X % k == 0]
        rng.shuffle(ks)
        success = False
        for k in ks[:3]:
            if time.monotonic() >= deadline or success:
                break
            N = X // k
            groups = _groups(N)
            rng.shuffle(groups)
            for m, kk, r in groups[:MAX_GROUPS]:
                now = time.monotonic()
                if now >= deadline:
                    break
                order, mul, inv = lib.semidirect_group(m, kk, r)
                T = [[mul(x, g) for g in range(N)] for x in range(N)]
                invs = [inv(g) for g in range(N)]
                gdl = min(deadline, now + GROUP_SEC)
                res = _anneal(k, N, d, D, T, invs, rng, gdl)
                if res is not None:
                    sig, volt = res
                    n, e = _lift_edges(k, N, d, T, sig, volt)
                    consider(n, e)
                    success = True
                    break
        if success:
            W = 4
        else:
            W = min(W + 2, 60)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
