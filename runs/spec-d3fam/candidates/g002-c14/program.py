import math
import random
import time

import lib


def _search_cover(m, d, rng, deadline):
    """Find S in Z_m with |S| = d, 0 in S, such that every nonzero x in Z_m is a difference s - t.

    The Haar graph H(Z_m, S) then has diameter <= 3, since a-a distances are at most 2 and
    a-b distances are at most 3. Simulated annealing minimises the number of uncovered differences.
    Returns the sorted list S, or None if the deadline passes first.
    """
    if d * (d - 1) < m - 1:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        cnt = [0] * m
        for i in range(d):
            for j in range(d):
                if i != j:
                    cnt[(S[i] - S[j]) % m] += 1
        cost = sum(1 for x in range(1, m) if cnt[x] == 0)
        T = 0.8
        for step in range(100000):
            if step % 2000 == 0 and time.monotonic() >= deadline:
                return None
            if cost == 0:
                return sorted(S)
            idx = rng.randrange(1, d)
            s = S[idx]
            r = rng.randrange(1, m)
            if r in S:
                continue
            others = S[:idx] + S[idx + 1:]
            delta = 0
            # Remove s's differences.
            for t in others:
                x = (s - t) % m
                cnt[x] -= 1
                if cnt[x] == 0:
                    delta += 1
                y = (t - s) % m
                cnt[y] -= 1
                if cnt[y] == 0:
                    delta += 1
            # Add r's differences.
            for t in others:
                x = (r - t) % m
                if cnt[x] == 0:
                    delta -= 1
                cnt[x] += 1
                y = (t - r) % m
                if cnt[y] == 0:
                    delta -= 1
                cnt[y] += 1
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[idx] = r
                cost += delta
            else:
                # Revert the move.
                for t in others:
                    cnt[(r - t) % m] -= 1
                    cnt[(t - r) % m] -= 1
                for t in others:
                    cnt[(s - t) % m] += 1
                    cnt[(t - s) % m] += 1
            T = max(0.15, T * 0.99997)
        if cost == 0:
            return sorted(S)
    return None


def _covering_haar(d, D, rng, deadline, best):
    """Ascend over cyclic group orders m, keeping the largest Haar graph whose covering set is found."""
    m = best[0] // 2 + 1 if best is not None else d + 1
    mmax = d * d - d + 1
    found = None
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        budget = min(deadline, now + max(0.5, 0.35 * (deadline - now)))
        S = _search_cover(m, d, rng, budget)
        if S is None:
            break
        n, edges = lib.haar_graph(m, S)
        if not lib.is_valid(n, edges, d, D):
            break
        found = (n, edges)
        m += 1
    return found


def _random_haar_fallback(d, D, rng, deadline):
    """Parent-style fallback: random Haar graphs checked by diameter."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
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
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    best = None
    if D == 3:
        # Safe structured base (the record constructions).
        base = None
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base

        # Bold attempt: abelian Haar graphs whose connection set covers all of Z_m as differences.
        if d >= 3:
            res = _covering_haar(d, D, rng, deadline, best)
            if res is not None and lib.is_valid(res[0], res[1], d, D):
                if best is None or res[0] > best[0]:
                    best = res

    if best is None:
        best = _random_haar_fallback(d, D, rng, deadline)
    return best
