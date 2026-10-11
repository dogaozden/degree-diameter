import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar graphs from difference covers (diameter 3).
#
# Haar graph H(m, S): a_i joins b_{i+s} for s in S, with S a k-subset of Z_m.
# It is bipartite, k-regular, and has 2m vertices.
#
# Diameter 3 holds iff S - S covers all of Z_m:
#   * same-side pairs a_i, a_i' are at distance 2 when i' - i is in S - S;
#   * cross pairs a_i, b_j are at distance 1 or 3, and S + S - S = Z_m
#     whenever S - S = Z_m, so every cross pair is within 3.
# Hence the order is 2m with m <= k^2 - k + 1 (the Moore-type bound 2(d^2-d+1)).
#
# This replaces the projective-plane/arc family of the parent. The search is a
# fast hill-climb on the number of uncovered residues, with a few moves that
# accept a worse cover at low probability to escape plateaus. Each candidate
# is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------


def _cover(k, m, rng, deadline):
    """Find a k-subset S of Z_m (containing 0) with S - S = Z_m, or return None."""
    if k == 1:
        return [0] if m == 1 else None
    if k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    zeros = sum(1 for r in range(1, m) if cnt[r] == 0)
    inS = set(S)
    it = 0
    while zeros > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        x = S[i]
        y = rng.randrange(1, m)
        if y in inS:
            continue
        others = [s for s in S if s != x]
        nz = zeros
        # remove x
        for s in others:
            for r in ((x - s) % m, (s - x) % m):
                cnt[r] -= 1
                if cnt[r] == 0:
                    nz += 1
        # add y
        for s in others:
            for r in ((y - s) % m, (s - y) % m):
                if cnt[r] == 0:
                    nz -= 1
                cnt[r] += 1
        if nz <= zeros or rng.random() < 0.03:
            S[i] = y
            inS.discard(x)
            inS.add(y)
            zeros = nz
        else:
            # undo the add
            for s in others:
                for r in ((y - s) % m, (s - y) % m):
                    cnt[r] -= 1
            # undo the remove
            for s in others:
                for r in ((x - s) % m, (s - x) % m):
                    cnt[r] += 1
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for all D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3 and d >= 1:
        k = d
        rng = random.Random(seed * 1000003 + d)
        m_max = k * k - k + 1
        lo = max(k, int(0.85 * m_max))

        def budget():
            now = time.monotonic()
            return min(deadline, now + max(1.0, 0.15 * (deadline - now)))

        found = None
        m = lo
        # Find a feasible modulus by descending from the starting guess.
        while m >= k and time.monotonic() < deadline:
            S = _cover(k, m, rng, budget())
            if S is not None:
                found = (m, S)
                break
            m -= 1

        # Climb upward while the search keeps succeeding.
        if found is not None:
            m = found[0] + 1
            while m <= m_max and time.monotonic() < deadline:
                S2 = _cover(k, m, rng, budget())
                if S2 is None:
                    break
                found = (m, S2)
                m += 1

        if found is not None:
            mm, S = found
            n, e = lib.haar_graph(mm, S)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
