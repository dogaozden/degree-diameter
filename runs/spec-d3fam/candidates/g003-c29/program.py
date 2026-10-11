import math
import random
import time

import lib


def _record_base(d, D):
    """Structured record-order base for D = 3, or None if no construction applies."""
    if D != 3:
        return None
    q = d - 1
    try:
        if q >= 2 and lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)
    except Exception:
        return None
    return None


def _diff_cover(k, m, rng, deadline, budget):
    """Anneal a k-subset S of Z_m (containing 0) whose difference set S-S covers all of Z_m.

    The Haar graph of Z_m with connection set S is bipartite, k-regular, and has diameter
    at most 3 exactly when S-S = Z_m. Returns S as a list, or None if the budget runs out.
    """
    if k < 2 or m < k or m - 1 > k * (k - 1):
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    cost = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.4
    it = 0
    while cost > 0:
        it += 1
        if it > budget or ((it & 1023) == 0 and time.monotonic() >= deadline):
            return None
        i = rng.randrange(1, k)
        x = S[i]
        y = rng.randrange(1, m)
        if y in S:
            continue
        old = cost
        # remove x
        for j in range(k):
            if j != i:
                for r in ((x - S[j]) % m, (S[j] - x) % m):
                    cnt[r] -= 1
                    if cnt[r] == 0:
                        cost += 1
        # add y
        for j in range(k):
            if j != i:
                for r in ((y - S[j]) % m, (S[j] - y) % m):
                    if cnt[r] == 0:
                        cost -= 1
                    cnt[r] += 1
        delta = cost - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
        else:
            # revert: remove y, add x
            for j in range(k):
                if j != i:
                    for r in ((y - S[j]) % m, (S[j] - y) % m):
                        cnt[r] -= 1
                        if cnt[r] == 0:
                            cost += 1
            for j in range(k):
                if j != i:
                    for r in ((x - S[j]) % m, (S[j] - x) % m):
                        if cnt[r] == 0:
                            cost -= 1
                        cnt[r] += 1
    return S


def _search_cover(k, m_start, deadline, rng):
    """Increase m from m_start while a difference cover of Z_m by k elements is found."""
    best = None
    m = max(m_start, k, 2)
    while m - 1 <= k * (k - 1) and time.monotonic() < deadline:
        S = None
        while S is None and time.monotonic() < deadline:
            S = _diff_cover(k, m, rng, deadline, 200000)
        if S is None:
            break
        best = (m, sorted(S))
        m += 1
    return best


def _generic_haar_search(d, D, rng, deadline):
    """Random Haar graphs with diameter <= D (used for D != 3 when no base applies)."""
    best = None
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
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    # Safe fallback first: a trivially valid graph.
    if D == 0:
        fallback = (1, [])
    elif D == 1:
        fallback = (2, [(0, 1)]) if d >= 1 else (1, [])
    else:
        fallback = (2, [(0, 1)]) if d >= 1 else (1, [])
        if d >= 1:
            kd = lib.haar_graph(d, range(d))
            if lib.is_valid(kd[0], kd[1], d, D):
                fallback = kd
    best = fallback

    try:
        base = _record_base(d, D)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base

        if D == 3 and d >= 2:
            # Different construction: Haar graph on Z_m with S-S = Z_m (diameter 3, degree d).
            # Starting at half the current best order means we only search for lifts that match
            # or beat the incumbent.
            m_start = max(d, best[0] // 2)
            res = _search_cover(d, m_start, deadline, rng)
            if res is not None:
                m, S = res
                n, edges = lib.haar_graph(m, S)
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
        elif best is fallback and D >= 2:
            res = _generic_haar_search(d, D, rng, deadline)
            if res is not None and lib.is_valid(res[0], res[1], d, D):
                if res[0] > best[0]:
                    best = res
    except Exception:
        pass

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
