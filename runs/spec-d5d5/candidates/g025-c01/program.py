import math
import random
import time

import lib

ITERS = 900          # annealing steps per (group, base lift) try
MAX_GROUPS = 10      # groups tried per (a, N) attempt
MAX_A = 6            # largest number of base vertices per side
T0_FACTOR = 2.0      # initial temperature, scaled by a
T1_FACTOR = 0.2      # final temperature, scaled by a


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-vertex base voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: a vertices A_0..A_{a-1} and a vertices B_0..B_{a-1}, d-regular.
# It is the union of d permutations p_0..p_{d-1} of range(a): dart (i, p_k[i])
# with voltage V[k][i] in G. Vertex (A_i, x) joins (B_j, x*g) for each dart
# (i, j, g). Left multiplication by h in G is an automorphism, and it is
# transitive on each fibre, so BFS from (A_i, e) and (B_j, e) decides the
# diameter. Darts are kept distinct, so the lift is exactly d-regular.
# Vertex indexing: A_i fibre occupies [i*N, (i+1)*N); B_j fibre occupies
# [a*N + j*N, a*N + (j+1)*N).
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


def _distinct(a, d, perms, V):
    """True if all darts (i, p_k[i], V[k][i]) are pairwise distinct."""
    seen = set()
    for k in range(d):
        p = perms[k]
        vk = V[k]
        for i in range(a):
            t = (i, p[i], vk[i])
            if t in seen:
                return False
            seen.add(t)
    return True


def _unreached(a, N, M, I, perms, V, d, D):
    """Count (source, vertex) pairs not within distance D, over one source per base vertex."""
    dfrom = [[] for _ in range(a)]
    dinto = [[] for _ in range(a)]
    for k in range(d):
        p = perms[k]
        vk = V[k]
        for i in range(a):
            j = p[i]
            g = vk[i]
            dfrom[i].append((j, g))
            dinto[j].append((i, I[g]))
    tot_v = 2 * a * N
    base_b = a * N
    total = 0
    for s in range(2 * a):
        src = s * N if s < a else base_b + (s - a) * N
        seen = bytearray(tot_v)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < base_b:
                    i, x = divmod(u, N)
                    row = M[x]
                    for j, g in dfrom[i]:
                        v = base_b + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - base_b, N)
                    row = M[y]
                    for i, gi in dinto[j]:
                        v = i * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += tot_v - count
    return total


def _edges(a, N, M, perms, V, d):
    """Materialise the lift as (n, edges)."""
    base_b = a * N
    edges = set()
    for k in range(d):
        p = perms[k]
        vk = V[k]
        for i in range(a):
            j = p[i]
            g = vk[i]
            for x in range(N):
                u = i * N + x
                v = base_b + j * N + M[x][g]
                edges.add((u, v) if u < v else (v, u))
    return 2 * a * N, sorted(edges)


def _anneal(a, N, M, I, d, D, rng, iters, deadline):
    """Simulated annealing over (permutations, voltages) to zero unreached pairs."""
    perms = [rng.sample(range(a), a) for _ in range(d)]
    V = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
    tries = 0
    while not _distinct(a, d, perms, V) and tries < 50:
        V = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
        tries += 1
    if not _distinct(a, d, perms, V):
        return None

    cur = _unreached(a, N, M, I, perms, V, d, D)
    T0 = T0_FACTOR * a
    T1 = T1_FACTOR * a
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / iters)
        k = rng.randrange(d)
        if a > 1 and rng.random() < 0.3:
            # Swap two targets within permutation k (keeps d-regularity).
            p = perms[k]
            i1, i2 = rng.sample(range(a), 2)
            p[i1], p[i2] = p[i2], p[i1]
            if _distinct(a, d, perms, V):
                v = _unreached(a, N, M, I, perms, V, d, D)
                if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                    cur = v
                    continue
            p[i1], p[i2] = p[i2], p[i1]
        else:
            # Change one voltage.
            i = rng.randrange(a)
            old = V[k][i]
            V[k][i] = rng.randrange(N)
            if _distinct(a, d, perms, V):
                v = _unreached(a, N, M, I, perms, V, d, D)
                if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                    cur = v
                    continue
            V[k][i] = old
    if cur == 0:
        return perms, V
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for base size a; return (perms, V, M) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        M = [[mul(x, g) for g in range(N)] for x in range(N)]
        I = [inv(g) for g in range(N)]
        st = _anneal(a, N, M, I, d, D, rng, ITERS, deadline)
        if st is not None:
            perms, V = st
            return perms, V, M
    return None


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

    if D == 1:
        consider(2, [(0, 1)])
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best if lib.is_valid(best[0], best[1], d, D) else (1, [])

    # Multi-vertex base lifts: only sizes that can beat the current best.
    Mb = lib._moore_bound(d, D)
    floor = max(best_n + 1, int(0.45 * Mb))
    cands = []
    for a in range(1, MAX_A + 1):
        for N in range(max(d, 1), Mb // (2 * a) + 1):
            size = 2 * a * N
            if floor <= size <= Mb:
                cands.append((size, a, N))
    cands.sort()

    budget = 0.3
    while time.monotonic() < deadline and cands:
        if not any(s > best_n for s, _, _ in cands):
            break
        success = False
        for size, a, N in cands:
            if size <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            perms, V, M = res
            n, e = _edges(a, N, M, perms, V, d)
            consider(n, e)
            success = True
        if not success:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
