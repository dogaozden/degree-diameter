import math
import random
import time

import lib


def _anneal(m, d, rng, deadline):
    """Find a d-subset S of Z_m (with 0 in S) whose difference set S-S covers all of Z_m \\ {0}.

    The bipartite Haar graph of Z_m with connection set S then has diameter 3:
    same-side pairs are at distance 2 (since j-i in S-S), and cross pairs at
    distance <= 3 (since S-S+S covers Z_m). Returns S or None on timeout.
    """
    if m < d or m - 1 > d * (d - 1):
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        cnt = [0] * m
        unc = m - 1                       # nonzero residues not yet covered
        for i in range(d):
            for j in range(d):
                if i != j:
                    r = (S[i] - S[j]) % m
                    cnt[r] += 1
                    if cnt[r] == 1:
                        unc -= 1
        T = 0.4
        for it in range(60000):
            if it & 1023 == 0 and time.monotonic() >= deadline:
                return None
            if unc == 0:
                return S
            k = rng.randrange(1, d)
            old = S[k]
            new = rng.randrange(m)
            if new in S:
                continue
            # Remove differences involving old.
            delta = 0
            for idx in range(d):
                if idx == k:
                    continue
                t = S[idx]
                for r in ((old - t) % m, (t - old) % m):
                    cnt[r] -= 1
                    if cnt[r] == 0:
                        delta += 1
            # Add differences involving new.
            for idx in range(d):
                if idx == k:
                    continue
                t = S[idx]
                for r in ((new - t) % m, (t - new) % m):
                    if cnt[r] == 0:
                        delta -= 1
                    cnt[r] += 1
            nu = unc + delta
            if nu <= unc or rng.random() < math.exp((unc - nu) / T):
                S[k] = new
                unc = nu
            else:
                # Revert: undo the additions of new, then the removals of old.
                for idx in range(d):
                    if idx == k:
                        continue
                    t = S[idx]
                    for r in ((new - t) % m, (t - new) % m):
                        cnt[r] -= 1
                for idx in range(d):
                    if idx == k:
                        continue
                    t = S[idx]
                    for r in ((old - t) % m, (t - old) % m):
                        cnt[r] += 1
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    best = None

    if D == 3 and d >= 3:
        # Structured record base, kept as the safe starting point.
        base = None
        q = d - 1
        if lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base

        # New construction: cyclic Haar graphs from difference covers.
        m = (best[0] // 2 + 1) if best is not None else d
        mmax = d * d - d + 1
        while m <= mmax and time.monotonic() < deadline:
            S = _anneal(m, d, rng, deadline)
            if S is None:
                break
            n, edges = lib.haar_graph(m, S)
            if not lib.is_valid(n, edges, d, D):
                break
            best = (n, edges)
            m += 1

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best

    # Fallback: random Haar graphs with connection sets containing 0.
    fb = lib.haar_graph(d, range(d))
    if not lib.is_valid(fb[0], fb[1], d, D):
        return 1, []
    best = fb
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
