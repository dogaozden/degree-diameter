import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: cyclic Haar graphs from difference covers (D = 3).
#
# H(Z_m, S) has parts a_i, b_i (i in Z_m), a_i ~ b_{i+s} for s in S. It is
# bipartite and |S|-regular on 2m vertices. Its diameter is at most 3 exactly
# when S - S covers all of Z_m (same-side pairs need a common neighbour, and
# cross pairs then reach within 3 steps). So we look for a difference cover S
# of size d with the largest modulus m, and output the Haar graph on 2m
# vertices. Since m <= d^2 - d + 1, the Moore-type ceiling is 2(d^2 - d + 1).
#
# A simulated-annealing search raises m one step at a time. Each step is a
# random restart until the cover is found or its time slice runs out.
#
# Fallbacks: the projective-plane arc (conic) construction, and K_{d,d}.
# Every candidate passes lib.is_valid before it can be returned.
# ----------------------------------------------------------------------------


def _drop(S, i, cnt, m):
    """Remove the difference contributions of S[i]; return the change in uncovered count."""
    x = S[i]
    delta = 0
    for j in range(len(S)):
        if j == i:
            continue
        t = S[j]
        r = (x - t) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            delta += 1
        r = (t - x) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            delta += 1
    return delta


def _put(S, i, v, cnt, m):
    """Add the difference contributions of value v placed at index i; return the change in uncovered count."""
    delta = 0
    for j in range(len(S)):
        if j == i:
            continue
        t = S[j]
        r = (v - t) % m
        cnt[r] += 1
        if cnt[r] == 1:
            delta -= 1
        r = (t - v) % m
        cnt[r] += 1
        if cnt[r] == 1:
            delta -= 1
    return delta


def _cover_attempt(m, k, rng, deadline):
    """Simulated annealing for a k-subset S of Z_m with S - S = Z_m. Returns S or None."""
    S = rng.sample(range(m), k)
    cnt = [0] * m
    for a in range(k):
        for b in range(k):
            if a != b:
                cnt[(S[a] - S[b]) % m] += 1
    cost = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.4
    it = 0
    while cost > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        if rng.random() < 0.8:
            # Aim the new element at an uncovered difference.
            y = -1
            for _ in range(20):
                r = rng.randrange(1, m)
                if cnt[r] == 0:
                    y = (r + S[rng.randrange(k)]) % m
                    break
            if y < 0:
                y = rng.randrange(m)
        else:
            y = rng.randrange(m)
        if y == x or y in S:
            continue
        delta = _drop(S, i, cnt, m)
        S[i] = y
        delta += _put(S, i, y, cnt, m)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost += delta
        else:
            _drop(S, i, cnt, m)
            S[i] = x
            _put(S, i, x, cnt, m)
    return list(S)


def _haar_cover(k, rng, deadline):
    """Largest m found (with a size-k difference cover of Z_m) as (m, S), or None."""
    best = None
    m = k + 1
    while time.monotonic() < deadline:
        if m - 1 > k * (k - 1):  # counting bound: impossible beyond this
            break
        found = None
        for _ in range(3):
            rem = deadline - time.monotonic()
            if rem <= 0:
                break
            budget = min(rem, max(1.0, 0.25 * rem))
            found = _cover_attempt(m, k, rng, min(deadline, time.monotonic() + budget))
            if found is not None:
                break
        if found is None:
            break
        best = (m, found)
        m += 1
    return best


# ----------------------------------------------------------------------------
# Conic / hyperoval arc extension of PG(2, q) (diameter 3). Fallback family.
# ----------------------------------------------------------------------------

def _conic_graph(d):
    """Projective plane incidence plus an arc-based extension, or None."""
    q = None
    for c in range(d - 1, 1, -1):
        if lib.is_prime_power(c):
            q = c
            break
    if q is None:
        return None
    s = d - q - 1
    n2, pe = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in pe:
        pl[u].append(v - m)
        lp[v - m].append(u)
    if s >= 2:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        pts = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
        if q % 2 == 0:
            pts.append((0, 1, 0))
        S = [index[p] for p in pts]
    else:
        S = []
    kk = len(S)
    base = 2 * m
    E = list(pe)
    for t, P in enumerate(S):
        x = base + t
        E.extend((x, m + L) for L in pl[P])
    for t, j in enumerate(S):
        b = base + kk + t
        E.extend((Q, b) for Q in lp[j])
    return base + 2 * kk, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.5)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        c = _conic_graph(d)
        if c is not None:
            consider(c[0], c[1])

        if d >= 2:
            rng = random.Random(seed * 1000003 + d)
            res = _haar_cover(d, rng, deadline)
            if res is not None:
                m, S = res
                n, e = lib.haar_graph(m, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
