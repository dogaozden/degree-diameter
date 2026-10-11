import math
import random
import time

import lib


# Idea: a Haar graph H(m, S) on Z_m is bipartite and d-regular when |S| = d. For diameter 3 it is
# enough that the nonzero differences S - S cover all of Z_m (this gives distance <= 2 between
# same-side vertices), and that S - S + S covers the rest of Z_m (this gives distance <= 3 across
# sides, which is almost always automatic). Random subsets of Z_m rarely cover Z_m for large m.
# So we search for such a "difference cover" with simulated annealing on the number of uncovered
# residues, then grow m one step at a time while the search still succeeds.

def _diff_counts(S, m):
    """cnt[x] = number of ordered pairs (s, t) in S, s != t, with s - t = x (mod m)."""
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    return cnt


def _anneal_difference_cover(m, k, rng, deadline, max_moves):
    """Find S subset of Z_m with |S| = k, 0 in S, and S - S covering all of Z_m \\ {0}.

    Simulated annealing: one move swaps one non-zero element of S for a fresh residue.
    Cost = number of uncovered residues, tracked incrementally in O(k) per move.
    Returns the list S, or None if the budget runs out.
    """
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = set(S)
    cnt = _diff_counts(S, m)
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    exp = math.exp
    for it in range(max_moves):
        if unc == 0:
            return list(S)
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        out = S[i]
        t = rng.randrange(1, m)
        if t in inS:
            continue
        temp = 0.12 + 0.9 * (1.0 - it / max_moves)
        others = [S[j] for j in range(k) if j != i]
        old = unc
        d_unc = 0
        # Remove the differences that involve `out`.
        for s in others:
            x = (out - s) % m
            y = (s - out) % m
            cnt[x] -= 1
            if cnt[x] == 0:
                d_unc += 1
            cnt[y] -= 1
            if cnt[y] == 0:
                d_unc += 1
        # Add the differences that involve `t`.
        for s in others:
            x = (t - s) % m
            y = (s - t) % m
            if cnt[x] == 0:
                d_unc -= 1
            cnt[x] += 1
            if cnt[y] == 0:
                d_unc -= 1
            cnt[y] += 1
        if d_unc <= 0 or rng.random() < exp(-d_unc / temp):
            S[i] = t
            inS.discard(out)
            inS.add(t)
            unc = old + d_unc
        else:
            # Undo: first the additions, then the removals.
            for s in others:
                cnt[(t - s) % m] -= 1
                cnt[(s - t) % m] -= 1
            for s in others:
                cnt[(out - s) % m] += 1
                cnt[(s - out) % m] += 1
    return list(S) if unc == 0 else None


def _search_haar_diam3(d, rng, deadline, best):
    """Grow m upward; at each m look for a difference cover of size d and keep the largest valid Haar graph."""
    m = max(d + 1, d * d // 2)
    fails = 0
    while fails < 3 and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(1.5, 0.3 * remaining))
        S = None
        while S is None and time.monotonic() < slice_end:
            S = _anneal_difference_cover(m, d, rng, slice_end, 60000)
        ok = False
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, 3):
                ok = True
                if n > best[0]:
                    best = (n, edges)
        if ok:
            fails = 0
        else:
            fails += 1
        m += 1
    return best


def _search_haar_generic(d, D, rng, deadline, best):
    """Random Haar search for other diameters (same idea as the parent)."""
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))

    # Projective plane incidence graph: optimal when d - 1 is a prime power and D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Trivial fallback, always valid.
    best = (1, [])
    if d < 2 or D < 1:
        return best

    # K_{d,d} is a valid fallback whenever its diameter (2) is within D.
    n0, e0 = lib.haar_graph(d, range(d))
    if lib.is_valid(n0, e0, d, D):
        best = (n0, e0)

    rng = random.Random(seed)
    if D == 3:
        best = _search_haar_diam3(d, rng, deadline, best)
    else:
        best = _search_haar_generic(d, D, rng, deadline, best)
    return best
