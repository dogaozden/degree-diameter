import math
import random
import time

import lib

ITERS = 500           # annealing steps per restart
RESTARTS = 3          # fresh random lifts per group before moving on
GROUPS_PER_CAND = 8   # groups tried per (base size, group order) candidate per attempt
MAX_A = 4             # base graph has a vertices per side
CAND_LIMIT = 40       # candidates tried per round
HEAD = 12             # smallest-above-best candidates always included


# ----------------------------------------------------------------------------
# Safe fallbacks (always validated by lib.is_valid before use).
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k with a BASE graph that has
# a vertices per side (not just one). The base is a d-regular bipartite
# multigraph given by d permutations pi_i of range(a) (dart u -> pi_i(u)),
# and every dart (u, i) carries a group element g = gel[u][i].
#
# Lift: A-vertex (u, x) is adjacent to B-vertex (v, x*g) for each dart (u, v, g).
# Left multiplication by G is an automorphism, so eccentricities are constant
# on each fibre; checking the 2a base vertices at x = identity is exact.
# Cost = number of (source, vertex) pairs at distance > D, plus a penalty for
# duplicate darts. Cost 0 means diameter <= D.
# a = 1 reproduces the bi-Cayley search as a special case.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _cost(a, N, T, outA, outB, D):
    """Total unreached (source, vertex) pairs for the 2a base-vertex sources."""
    nodes = 2 * a * N
    split = a * N
    total = 0
    for s in range(2 * a):
        seen = bytearray(nodes)
        src = s * N
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for node in frontier:
                if node < split:
                    u, x = divmod(node, N)
                    row = T[x]
                    for v, g in outA[u]:
                        w = (a + v) * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    base, y = divmod(node, N)
                    row = T[y]
                    for u, h in outB[base - a]:
                        w = u * N + row[h]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += nodes - count
    return total


def _score(a, d, N, T, I, D, perms, gel):
    outA = [[] for _ in range(a)]
    outB = [[] for _ in range(a)]
    darts = set()
    pen = 0
    for u in range(a):
        for i in range(d):
            v = perms[i][u]
            g = gel[u][i]
            key = (u, v, g)
            if key in darts:
                pen += 1
            darts.add(key)
            outA[u].append((v, g))
            outB[v].append((u, I[g]))
    return _cost(a, N, T, outA, outB, D) + 10000 * pen


def _anneal(a, d, N, T, I, D, rng, deadline, iters):
    perms = []
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        perms.append(p)
    gel = [[rng.randrange(N) for _ in range(d)] for _ in range(a)]
    cur = _score(a, d, N, T, I, D, perms, gel)
    for it in range(iters):
        if cur == 0:
            return perms, gel
        if time.monotonic() > deadline:
            return None
        temp = max(0.3, 2.0 * (1.0 - it / iters))
        if a >= 2 and rng.random() < 0.3:
            i = rng.randrange(d)
            p, q = rng.sample(range(a), 2)
            perms[i][p], perms[i][q] = perms[i][q], perms[i][p]
            new = _score(a, d, N, T, I, D, perms, gel)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                perms[i][p], perms[i][q] = perms[i][q], perms[i][p]
        else:
            u = rng.randrange(a)
            i = rng.randrange(d)
            old = gel[u][i]
            gel[u][i] = rng.randrange(N)
            new = _score(a, d, N, T, I, D, perms, gel)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                gel[u][i] = old
    return (perms, gel) if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_CAND]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        I = [inv(g) for g in range(N)]
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            res = _anneal(a, d, N, T, I, D, rng, deadline, ITERS)
            if res is not None:
                return res, T
    return None


def _edges(a, d, N, T, perms, gel):
    edges = []
    for u in range(a):
        for i in range(d):
            v = perms[i][u]
            g = gel[u][i]
            for x in range(N):
                edges.append((u * N + x, (a + v) * N + T[x][g]))
    return 2 * a * N, edges


def _cands(best_n, M, d):
    out = []
    for a in range(1, MAX_A + 1):
        hi = M // (2 * a)
        lo = max(best_n // (2 * a) + 1, d + 1)
        for N in range(lo, hi + 1):
            out.append((2 * a * N, a, N))
    out.sort()
    if len(out) > CAND_LIMIT:
        head = out[:HEAD]
        rest = out[HEAD:]
        n_rest = CAND_LIMIT - HEAD
        step = len(rest) / n_rest
        out = head + [rest[int(i * step)] for i in range(n_rest)]
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Calibration case with an exact construction.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        if best[0] == n:
            return best

    # Safe fallbacks.
    if D >= 2 and d >= 1:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    M = lib.moore_bound(d, D)
    budget = 0.5
    while time.monotonic() < deadline:
        cands = [c for c in _cands(best[0], M, d) if c[0] > best[0]]
        if not cands:
            break
        found_any = False
        for total, a, N in cands:
            if time.monotonic() >= deadline:
                break
            if total <= best[0]:
                continue
            att_deadline = min(deadline, time.monotonic() + budget)
            res = _attempt(a, N, d, D, rng, att_deadline)
            if res is None:
                continue
            (perms, gel), T = res
            n, e = _edges(a, d, N, T, perms, gel)
            consider(n, e)
            found_any = True
        if not found_any:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
