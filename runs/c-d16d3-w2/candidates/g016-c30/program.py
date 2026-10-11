import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Difference-cover Haar graphs (diameter 3).
#
# Let G be a finite abelian group of order m and S a subset of G with |S| = k.
# The Haar graph H(G, S) has parts A = {A_g} and B = {B_g}, with A_g adjacent to
# B_{g+s} for every s in S. It is bipartite and k-regular on 2m vertices.
#
# If every nonzero element of G is a difference s - s' with s, s' in S (S is a
# "difference cover"), then the diameter is at most 3:
#   * A_g to A_h (and B to B) is distance 2 via a difference h - g,
#   * A_g to B_t is distance 1 if t - g is in S, and otherwise distance 3, since
#     S - S + S = G whenever S - S = G.
# With |S| = d this gives orders up to 2(d(d-1)+1), the Moore-type ceiling.
# The record for d = 16 is 394 = 2 * 197, so we search for covers of order
# m >= 198 in Z_m or in Z_a x Z_b. The fallback is K_{d,d}, which has diameter 2.
# ----------------------------------------------------------------------------


def _sub_table(a, b):
    """Subtraction table of Z_a x Z_b, element (x, y) coded as x*b + y."""
    m = a * b
    vd = [divmod(v, b) for v in range(m)]
    sub = []
    for u in range(m):
        x1, y1 = divmod(u, b)
        sub.append([((x1 - x2) % a) * b + (y1 - y2) % b for x2, y2 in vd])
    return sub


def _add(a, b, g, s):
    """Addition in Z_a x Z_b with the same coding."""
    gx, gy = divmod(g, b)
    sx, sy = divmod(s, b)
    return ((gx + sx) % a) * b + (gy + sy) % b


def _find_cover(m, sub, k, rng, deadline):
    """Simulated annealing for a k-subset S of the group whose differences cover all nonzero elements.

    Returns the list S on success, or None if the deadline passes or the search stalls.
    """
    S = rng.sample(range(m), k)
    inS = set(S)
    cnt = [0] * m  # cnt[x] = number of ordered pairs (s, s') in S with s - s' = x
    for i in range(k):
        si = sub[S[i]]
        for j in range(k):
            if i != j:
                cnt[si[S[j]]] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)

    def move(i, v):
        """Replace S[i] by v, update cnt, and return the change in the number of uncovered differences."""
        old = S[i]
        ro = sub[old]
        rv = sub[v]
        delta = 0
        for j in range(k):
            if j == i:
                continue
            x = S[j]
            for dd in (ro[x], sub[x][old]):
                cnt[dd] -= 1
                if cnt[dd] == 0:
                    delta += 1
            for dd in (rv[x], sub[x][v]):
                if cnt[dd] == 0:
                    delta -= 1
                cnt[dd] += 1
        S[i] = v
        return delta

    T = 0.4
    best_unc = unc
    since = 0
    it = 0
    while unc > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        since += 1
        if since > 40000:
            return None
        i = rng.randrange(k)
        v = rng.randrange(m)
        if v in inS or v == S[i]:
            continue
        old = S[i]
        delta = move(i, v)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            unc += delta
            inS.discard(old)
            inS.add(v)
            if unc < best_unc:
                best_unc = unc
                since = 0
        else:
            move(i, old)
    return list(S)


def _cover_search(d, D, deadline, rng, base):
    """Search for difference-cover Haar graphs of growing order; return the best valid (n, edges) found.

    `base` is the already-valid fallback (n, edges). Every candidate is checked with lib.is_valid.
    """
    k = d
    hi = k * (k - 1) + 1  # Moore-type limit for a difference cover of size k
    best_n, best_edges = base
    best_m = best_n // 2
    while time.monotonic() < deadline:
        lo = max(best_m + 1, k)
        cands = list(range(lo, min(hi, lo + 3) + 1))
        if not cands:
            break
        m = rng.choice(cands)
        divs = [a for a in range(1, m + 1) if m % a == 0]
        a = rng.choice(divs)  # a = 1 gives the cyclic group Z_m
        b = m // a
        sub = _sub_table(a, b)
        end = min(deadline, time.monotonic() + 3.0)
        S = _find_cover(m, sub, k, rng, end)
        if S is None:
            continue
        edges = []
        for g in range(m):
            for s in S:
                edges.append((g, m + _add(a, b, g, s)))
        n = 2 * m
        if n > best_n and lib.is_valid(n, edges, d, D):
            best_n, best_edges = n, edges
            best_m = m
    return best_n, best_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed * 1000003 + d * 131 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = (fallback[0], list(fallback[1]))

    if D >= 3 and d >= 2:
        best = _cover_search(d, D, deadline, rng, best)

    n, edges = best
    if not lib.is_valid(n, edges, d, D):
        return fallback[0], list(fallback[1])
    return n, edges
