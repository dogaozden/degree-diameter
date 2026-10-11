import math
import random
import time

import lib


def _change(cnt, others, old, new, m):
    """Replace difference contributions of `old` by those of `new` (against `others`).

    cnt[g] counts ordered differences equal to g (mod m) inside the current set.
    Returns the change in the number of uncovered nonzero residues.
    Calling it again with (new, old) exactly reverts the change.
    """
    delta = 0
    for t in others:
        for g in ((old - t) % m, (t - old) % m):
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
    for t in others:
        for g in ((new - t) % m, (t - new) % m):
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
    return delta


def _cover(m, k, rng, deadline):
    """Search a k-subset S of Z_m (containing 0) whose difference set covers all of Z_m \\ {0}.

    The bipartite graph Haar(m, S) then has diameter 3 (same-side pairs at distance <= 2,
    cross pairs at distance <= 3). Simulated annealing on the number of uncovered residues.
    Returns the sorted subset, or None if the deadline passes first.
    """
    inS = [False] * m
    S = [0] + rng.sample(range(1, m), k - 1)
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    uncov = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 0.35
    it = 0
    while True:
        if uncov == 0:
            return sorted(S)
        it += 1
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, k)          # keep S[0] = 0 fixed (WLOG by translation)
        old = S[i]
        x = rng.randrange(1, m)
        while inS[x]:
            x = rng.randrange(1, m)
        others = S[:i] + S[i + 1:]
        delta = _change(cnt, others, old, x, m)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            inS[old] = False
            inS[x] = True
            uncov += delta
        else:
            _change(cnt, others, x, old, m)  # revert


def _base3(d):
    """Structured D = 3 base graph with max degree d (or None)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        n, edges = lib.projective_plane_incidence(q)   # degree q+1 = d
        if lib.is_valid(n, edges, d, 3):
            return n, edges
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        n, edges = lib.araujo_lopez_graph(d - 2)       # degree d
        if lib.is_valid(n, edges, d, 3):
            return n, edges
    return None


def _build3(d, seed, deadline):
    """Bi-Cayley (Haar) search for diameter 3: largest m with a diameter-covering d-set in Z_m."""
    rng = random.Random(seed)
    best = _base3(d)
    base_n = best[0] if best else 0
    mmax = d * d - d + 1                 # Moore-type limit on one side
    lo = base_n // 2 + 1                 # only try to beat the structured base
    ms = [m for m in range(mmax, lo - 1, -1) if m > d]
    for idx, m in enumerate(ms):
        now = time.monotonic()
        left = deadline - now
        if left <= 0:
            break
        slice_t = left / (len(ms) - idx)
        S = _cover(m, d, rng, now + slice_t)
        if S is None:
            continue
        n = 2 * m
        edges = lib.haar_graph(m, S)
        if lib.is_valid(n, edges, d, 3):
            best = (n, edges)
            break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if D == 3 and d >= 3:
        deadline = start + 0.8 * time_limit
        best = _build3(d, seed, deadline)
        if best is not None and lib.is_valid(best[0], best[1], d, D):
            return best
        return lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2

    # Other diameters: random Haar graph search (unchanged fallback).
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))       # complete bipartite K_{d,d}: always valid
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
