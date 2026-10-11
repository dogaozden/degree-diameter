import math
import random
import time

import lib

ITERS = 700            # annealing steps per group try
GROUPS_PER_TRY = 12    # groups tried for one (k, N) target within one attempt
# (base vertices per side, selection weight). k = 1 is plain bi-Cayley.
KS = [(2, 3), (3, 3), (4, 2), (1, 1)]


# ----------------------------------------------------------------------------
# Multi-orbit lifts over semidirect products Z_m x| Z_k.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, with d darts
# (i, j, g) built from d random permutations of range(k), so every base vertex
# has degree d. Lift: vertex A(i, x) is adjacent to B(j, x*g) for each dart.
# Left multiplication is an automorphism, so the diameter is checked from only
# the 2k sources A(i, e) and B(j, e). Multiple darts in the same base cell use
# distinct voltages, so the lift is simple.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, kk, r) with m*kk = N, giving Z_m x|_r Z_kk."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _unreached(k, N, T, darts, D):
    """Count (source, vertex) pairs at distance > D over the 2k base sources."""
    V = 2 * k * N
    off = k * N
    adj = [[] for _ in range(V)]
    for i, j, g in darts:
        ai = i * N
        bj = off + j * N
        for x in range(N):
            a = ai + x
            b = bj + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    sources = [i * N for i in range(k)] + [off + j * N for j in range(k)]
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


def _search(k, N, d, D, rng, deadline):
    """Anneal voltages over several groups of order N. Return (T, darts) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]

        darts = []
        for _ in range(d):
            perm = list(range(k))
            rng.shuffle(perm)
            for i in range(k):
                darts.append([i, perm[i], 0])
        used = {}
        for dart in darts:
            key = (dart[0], dart[1])
            s = used.setdefault(key, set())
            g = rng.randrange(N)
            while g in s:
                g = rng.randrange(N)
            s.add(g)
            dart[2] = g

        cur = _unreached(k, N, T, darts, D)
        for it in range(ITERS):
            if cur == 0 or time.monotonic() > deadline:
                break
            t = rng.randrange(len(darts))
            i, j, old = darts[t]
            cand = rng.randrange(N)
            clash = False
            for s in range(len(darts)):
                if s != t and darts[s][0] == i and darts[s][1] == j and darts[s][2] == cand:
                    clash = True
                    break
            if clash:
                continue
            darts[t][2] = cand
            v = _unreached(k, N, T, darts, D)
            temp = 2.0 * (1.0 - it / ITERS) + 0.1
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                darts[t][2] = old
        if cur == 0:
            return T, darts
    return None


def _edges(k, N, T, darts):
    """Expand a multi-orbit lift into (vertex count, edge list)."""
    off = k * N
    E = []
    for i, j, g in darts:
        for x in range(N):
            E.append((i * N + x, off + j * N + T[x][g]))
    return 2 * k * N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = [n0, e0]
    if not lib.is_valid(n0, e0, d, D):
        return 1, []

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    if D == 2:
        return best[0], best[1]

    # Incidence graph of PG(2, q), q + 1 <= d, diameter 3.
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            consider(*lib.projective_plane_incidence(q))
            break
    if D == 3 and lib.is_prime_power(d - 1):
        return best[0], best[1]

    moore = lib._moore_bound(d, D)
    budget = 3.0
    while time.monotonic() < deadline:
        feasible = []
        for k, w in KS:
            if k > d:
                continue
            N = max(d, best[0] // (2 * k) + 1)
            if 2 * k * N <= moore:
                feasible.append((k, N, w))
        if not feasible:
            break
        ks = [(k, N) for k, N, _ in feasible]
        ws = [w for _, _, w in feasible]
        k, N = rng.choices(ks, weights=ws)[0]
        if rng.random() < 0.3 and 2 * k * (N + 1) <= moore:
            N += 1

        att_deadline = min(deadline, time.monotonic() + budget)
        res = _search(k, N, d, D, rng, att_deadline)
        if res is not None:
            T, darts = res
            n, e = _edges(k, N, T, darts)
            consider(n, e)
        else:
            budget = min(budget * 1.25, 20.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return n0, e0
    return best[0], best[1]
