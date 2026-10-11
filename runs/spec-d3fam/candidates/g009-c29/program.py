import math
import random
import time

import lib


def _structured(d, D):
    """Algebraic D = 3 base graphs (projective plane or Araujo-Pardo-Lopez), validated, or None."""
    if D != 3:
        return None
    q = d - 1
    base = None
    if q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
    elif d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        return base
    return None


def _try_cover(m, k, rng, deadline):
    """Find k residues S (0 in S) with S - S = Z_m, by annealing; return S or None.

    The Haar graph H(m, S) is bipartite, k-regular, and has diameter <= 3 exactly
    when S - S covers Z_m. cnt[x] counts ordered pairs with difference x; unc counts
    nonzero residues with cnt = 0.
    """
    if m - 1 > k * (k - 1):
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    T = 0.6
    it = 0
    while unc > 0:
        it += 1
        if it & 255 == 0 and time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, k)
        old = S[i]
        if rng.random() < 0.5:
            holes = [x for x in range(1, m) if cnt[x] == 0]
            v = (rng.choice(S) + rng.choice(holes)) % m   # targeted: creates a hole-difference
        else:
            v = rng.randrange(m)
        if inS[v]:
            continue
        others = [S[j] for j in range(k) if j != i]
        new = unc
        # remove old element's differences
        for t in others:
            x = (old - t) % m
            cnt[x] -= 1
            if cnt[x] == 0:
                new += 1
            y = (t - old) % m
            cnt[y] -= 1
            if cnt[y] == 0:
                new += 1
        # add new element's differences
        for t in others:
            x = (v - t) % m
            if cnt[x] == 0:
                new -= 1
            cnt[x] += 1
            y = (t - v) % m
            if cnt[y] == 0:
                new -= 1
            cnt[y] += 1
        if new <= unc or rng.random() < math.exp((unc - new) / T):
            S[i] = v
            inS[old] = False
            inS[v] = True
            unc = new
        else:
            for t in others:
                cnt[(v - t) % m] -= 1
                cnt[(t - v) % m] -= 1
            for t in others:
                cnt[(old - t) % m] += 1
                cnt[(t - old) % m] += 1
    return S


def _haar_fallback(d, D, rng, deadline):
    """Random Haar graph search (generic fallback, always returns a valid graph)."""
    best = lib.haar_graph(d, range(d))          # K_{d,d}: always valid
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
    if d < 1:
        return 1, []
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    best = _structured(d, D)

    # Bold change for D = 3: bipartite Haar graphs H(m, S) with |S| = d and S - S = Z_m.
    # These give order 2m; search for m above the structured base's half-order.
    if D == 3 and d >= 3:
        m = d + 1 if best is None else max(d + 1, best[0] // 2 + 1)
        while m - 1 <= d * (d - 1) and time.monotonic() < deadline:
            S = _try_cover(m, d, rng, deadline)
            if S is None:
                break
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
            m += 1

    if best is None:
        best = _haar_fallback(d, D, rng, deadline)
    return best
