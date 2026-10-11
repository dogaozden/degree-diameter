import math
import random
import time

import lib


def _structured_base(d, D):
    """Structured D = 3 bases: PG(2,q) incidence or the Araujo-Pardo & Lopez graph. None otherwise."""
    if D != 3:
        return None
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)      # order 2(q^2+q+1), degree q+1
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)          # order 2(q^2+q+5), degree q+2 = d
    return None


def _pairs(s, others, sign, m, cnt, unc):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between s and each x in others."""
    for x in others:
        for k in ((s - x) % m, (x - s) % m):
            if k:
                old = cnt[k]
                new = old + sign
                cnt[k] = new
                if old == 0 and new > 0:
                    unc[0] -= 1
                elif old > 0 and new == 0:
                    unc[0] += 1


def _haar_search(m, d, rng, deadline):
    """Find S of size d in Z_m with 0 in S and S - S = Z_m, by annealing with random restarts.

    The Haar graph H(m, S) then has diameter <= 3: every a-a and b-b distance is covered
    by S - S, and every a-b distance by (S - S) + S = Z_m.
    Returns S, or None if the deadline passes first.
    """
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        cnt = [0] * m
        unc = [m - 1]                       # number of nonzero residues not yet a difference
        for i in range(d):
            for j in range(i + 1, d):
                _pairs(S[i], [S[j]], 1, m, cnt, unc)
        it = 0
        T = 0.6
        stuck_limit = 40000
        while unc[0] > 0 and it < stuck_limit:
            it += 1
            if (it & 255) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)         # never move the fixed element 0
            s = S[i]
            t = rng.randrange(1, m)
            if t in S:
                continue
            others = S[:i] + S[i + 1:]
            old = unc[0]
            _pairs(s, others, -1, m, cnt, unc)
            _pairs(t, others, 1, m, cnt, unc)
            new = unc[0]
            if new <= old or rng.random() < math.exp((old - new) / T):
                S[i] = t
            else:
                _pairs(t, others, -1, m, cnt, unc)
                _pairs(s, others, 1, m, cnt, unc)
        if unc[0] == 0:
            return S
    return None


def _haar_improve(best, d, D, rng, deadline):
    """Try cyclic Haar graphs of increasing side m above the current best order, keeping valid wins only."""
    n0, _ = best
    cap = d * (d - 1) + 1                   # largest m with S - S = Z_m possible for |S| = d
    m = max(d, n0 // 2 + 1)
    while m <= cap:
        now = time.monotonic()
        if now >= deadline:
            break
        S = _haar_search(m, d, rng, now + 0.5 * (deadline - now))
        if S is None:
            break
        n, edges = lib.haar_graph(m, S)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    best = None
    base = _structured_base(d, D)
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        best = base

    if D == 3 and d >= 3:
        if best is None:
            best = lib.haar_graph(d, range(d))           # K_{d,d}: always valid
        deadline = start + 0.7 * time_limit
        return _haar_improve(best, d, D, rng, deadline)

    if best is not None:
        return best

    # Fallback for other diameters: random Haar graphs (parent approach).
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
    deadline = start + 0.75 * time_limit
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
