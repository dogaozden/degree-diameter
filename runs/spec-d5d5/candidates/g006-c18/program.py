import math
import random
import time

import lib

ITERS = 100000          # annealing steps per try; the deadline is the real limit
NGROUPS = 6             # groups tried per attempt
BLOCK_COUNTS = (2, 3, 4, 5)


# ----------------------------------------------------------------------------
# Baselines (instant, always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-block voltage lifts over semidirect products Z_m x| Z_k.
#
# Idea (new relative to single-block bi-Cayley search): the base graph has b
# vertices on each side, A_0..A_{b-1} and B_0..B_{b-1}. Its d-regularity is
# encoded as d "layers", each a permutation p_t of range(b): A_i is joined to
# B_{p_t(i)} through voltage g_{t,i}. Each layer is a perfect matching of the
# base multigraph, and by Konig's theorem every d-regular bipartite multigraph
# decomposes this way, so the layered form loses no generality. The lift has
# 2bN vertices and is bipartite by construction.
#
# Left multiplication by G is an automorphism of the lift, so the diameter is
# at most D iff every base vertex (A_i, e) and (B_j, e) has eccentricity <= D.
# The annealer minimises the number of unreached pairs from those 2b sources.
# Moves: change one voltage, or swap two targets within one layer.
# Duplicate darts (same i, j, g) are rejected, so every lift edge is distinct
# and the degree is exactly d.
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


def _outs(perms, volt, b, d):
    """outs[i] = list of (j, g) darts leaving A_i."""
    return [[(perms[t][i], volt[t][i]) for t in range(d)] for i in range(b)]


def _valid(outs, d):
    """True if no two darts leaving the same A_i coincide (keeps the lift simple, degree d)."""
    return all(len(set(o)) == d for o in outs)


def _cost(b, N, D, T, ginv, outs):
    """Number of (source, vertex) pairs at distance > D, over the 2b base sources."""
    ins = [[] for _ in range(b)]
    for i in range(b):
        for j, g in outs[i]:
            ins[j].append((i, g))
    bN = b * N
    V = 2 * bN
    srcs = [i * N for i in range(b)] + [(b + j) * N for j in range(b)]
    total = 0
    for src in srcs:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in outs[i]:
                        v = (b + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
                    row = T[y]
                    for i, g in ins[j]:
                        v = i * N + row[ginv[g]]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(b, N, d, D, T, ginv, rng, deadline):
    """Anneal layered permutations and voltages to zero unreached pairs. Returns (perms, volt) or None."""
    perms = []
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        perms.append(p)
    volt = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
    for _ in range(100):
        outs = _outs(perms, volt, b, d)
        if _valid(outs, d):
            break
        volt = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
    else:
        return None

    cur = _cost(b, N, D, T, ginv, outs)
    iters = ITERS
    for it in range(iters):
        if cur == 0:
            return perms, volt
        if time.monotonic() > deadline:
            break
        temp = max(0.3, 2.0 * (1.0 - it / iters))
        if rng.random() < 0.6:
            t = rng.randrange(d)
            i = rng.randrange(b)
            old = volt[t][i]
            new = rng.randrange(N)
            if new == old:
                continue
            volt[t][i] = new
            outs2 = _outs(perms, volt, b, d)
            if not _valid(outs2, d):
                volt[t][i] = old
                continue
            v = _cost(b, N, D, T, ginv, outs2)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[t][i] = old
        else:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(b), 2)
            perms[t][i1], perms[t][i2] = perms[t][i2], perms[t][i1]
            outs2 = _outs(perms, volt, b, d)
            if not _valid(outs2, d):
                perms[t][i1], perms[t][i2] = perms[t][i2], perms[t][i1]
                continue
            v = _cost(b, N, D, T, ginv, outs2)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                perms[t][i1], perms[t][i2] = perms[t][i2], perms[t][i1]
    if cur == 0:
        return perms, volt
    return None


def _attempt(N, b, d, D, rng, deadline, ngroups):
    """Try several groups of order N with b base blocks per side. Returns (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    groups = groups[:ngroups]
    for idx, (m, k, r) in enumerate(groups):
        now = time.monotonic()
        if now > deadline:
            return None
        group_dl = now + (deadline - now) / (len(groups) - idx)
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]
        res = _anneal(b, N, d, D, T, ginv, rng, group_dl)
        if res is not None:
            perms, volt = res
            darts = [(i, b + perms[t][i], volt[t][i]) for i in range(b) for t in range(d)]
            return lib.group_lift(2 * b, darts, N, mul)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best[0], best[1]

    Mmax = lib._moore_bound(d, D)
    Nnext = {b: None for b in BLOCK_COUNTS}
    slice_ = {b: 2.0 for b in BLOCK_COUNTS}

    while time.monotonic() < deadline:
        ran = False
        for b in BLOCK_COUNTS:
            now = time.monotonic()
            if now >= deadline:
                break
            lower = max(best[0] // (2 * b) + 1, d)
            N = max(lower, Nnext[b] or lower)
            if 2 * b * N > Mmax:
                continue
            ran = True
            att_dl = min(deadline, now + slice_[b])
            res = _attempt(N, b, d, D, rng, att_dl, NGROUPS)
            if res is not None:
                consider(*res)
                Nnext[b] = N + 1
                slice_[b] = max(2.0, slice_[b] / 1.25)
            else:
                Nnext[b] = N
                slice_[b] = min(30.0, slice_[b] * 1.25)
        if not ran:
            break

    return best[0], best[1]
