import math
import random
import time

import lib

ITERS = 1500        # annealing steps per restart
MAX_K = 12          # maximum base vertices per side
MIN_GROUP = 8       # smallest group order worth searching
RATCHET_WIDTH = 7   # candidate orders tried per sweep

_group_cache = {}


# ----------------------------------------------------------------------------
# Safe fallbacks (always validated before use).
# ----------------------------------------------------------------------------

def _fallback(d, D):
    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 1 and D >= 1:
        consider(2, [(0, 1)])
    if d == 2 and D >= 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
    if d >= 2 and D >= 2:
        consider(*lib.haar_graph(d, range(d)))          # K_{d,d}, diameter 2
    if D == 3 and d >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
    return best


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect groups Z_m x|_r Z_k.
#
# Base graph: k "A" vertices and k "B" vertices, d layers. Layer l is a
# permutation perm[l] matching A_i to B_{perm[l][i]} with voltage volt[l][i].
# The lift has 2*k*N vertices, is bipartite and d-regular (up to duplicates).
# Left multiplication by G is an automorphism, so the sources for distance
# checks are one vertex per base vertex (2k sources).
# ----------------------------------------------------------------------------

def _groups(N):
    if N in _group_cache:
        return _group_cache[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _group_cache[N] = out
    return out


def _table(N, m, k, r):
    _, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    return mul, T


def _cost(k, N, T, perm, volt, d, D):
    """Total (source, vertex) pairs not within distance D over the 2k base sources."""
    nb = 2 * k
    n = nb * N
    adj = [[] for _ in range(n)]
    for l in range(d):
        pl = perm[l]
        vl = volt[l]
        for i in range(k):
            j = pl[i]
            g = vl[i]
            a_off = i * N
            b_off = (k + j) * N
            for x in range(N):
                a = a_off + x
                b = b_off + T[x][g]
                adj[a].append(b)
                adj[b].append(a)
    total = 0
    for s in range(nb):
        src = s * N
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
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
        total += n - count
    return total


def _anneal(k, N, T, d, D, rng, iters, deadline):
    perm = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
    cur = _cost(k, N, T, perm, volt, d, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 0.3 + 2.0 * (1.0 - it / iters)
        l = rng.randrange(d)
        if k > 1 and rng.random() < 0.4:
            i1, i2 = rng.sample(range(k), 2)
            pl = perm[l]
            pl[i1], pl[i2] = pl[i2], pl[i1]
            new = _cost(k, N, T, perm, volt, d, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                pl[i1], pl[i2] = pl[i2], pl[i1]
        else:
            i = rng.randrange(k)
            old = volt[l][i]
            nv = rng.randrange(N)
            if nv == old:
                continue
            volt[l][i] = nv
            new = _cost(k, N, T, perm, volt, d, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                volt[l][i] = old
    if cur == 0:
        return perm, volt
    return None


def _lift_edges(k, N, mul, perm, volt, d):
    darts = [(i, k + perm[l][i], volt[l][i]) for l in range(d) for i in range(k)]
    return lib.group_lift(2 * k, darts, N, mul)


def _try_n(n, d, D, rng, deadline):
    opts = []
    for k in range(1, MAX_K + 1):
        if n % (2 * k) == 0:
            N = n // (2 * k)
            if N >= MIN_GROUP:
                opts.append((k, N))
    if not opts:
        return None
    while time.monotonic() < deadline:
        k, N = rng.choice(opts)
        m, kk, r = rng.choice(_groups(N))
        mul, T = _table(N, m, kk, r)
        res = _anneal(k, N, T, d, D, rng, ITERS, deadline)
        if res is not None:
            perm, volt = res
            nn, edges = _lift_edges(k, N, mul, perm, volt, d)
            if lib.is_valid(nn, edges, d, D):
                return nn, edges
    return None


def _candidates(best_n, cap, count):
    out = []
    n = 2 * (best_n // 2 + 1)
    while n <= cap and len(out) < count:
        if any(n % (2 * k) == 0 and n // (2 * k) >= MIN_GROUP for k in range(1, MAX_K + 1)):
            out.append(n)
        n += 2
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    best = _fallback(d, D)
    if d < 3 or D < 2:
        return best
    if D == 3 and lib.is_prime_power(d - 1):
        return best   # projective plane incidence already meets the Moore bound

    rng = random.Random(seed)
    cap = lib._moore_bound(d, D)
    best_n = best[0]
    budget = 2.0

    while time.monotonic() < deadline:
        cands = _candidates(best_n, cap, RATCHET_WIDTH)
        if not cands:
            break
        progressed = False
        for n in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _try_n(n, d, D, rng, min(deadline, now + budget))
            if res is not None:
                best = res
                best_n = res[0]
                progressed = True
                break
        if not progressed:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
