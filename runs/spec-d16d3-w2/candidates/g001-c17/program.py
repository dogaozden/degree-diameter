import math
import random
import time

import lib


def _pg_candidate(d, D):
    """Incidence graph of PG(2, q) for the largest prime power q <= d-1 (degree q+1 <= d, diameter 3)."""
    if D < 3:
        return None
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2 or q > 150:
        return None
    return lib.projective_plane_incidence(q)


def _apply(cnt, st, m, x, others, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between x and each element of others.

    cnt[t] counts ordered differences equal to t (t in 1..m-1); st[0] = number of uncovered residues.
    """
    for y in others:
        r = (x - y) % m
        s = m - r
        for t in (r, s):
            if sign > 0:
                if cnt[t] == 0:
                    st[0] -= 1
                cnt[t] += 1
            else:
                cnt[t] -= 1
                if cnt[t] == 0:
                    st[0] += 1


def _sa(S, m, cap, deadline, rng):
    """Simulated annealing: adjust S (0 fixed as first element) so that S - S covers Z_m. Returns success."""
    k = len(S)
    cnt = [0] * m
    st = [m - 1]
    for i in range(k):
        for j in range(i + 1, k):
            r = (S[i] - S[j]) % m
            for t in (r, m - r):
                if cnt[t] == 0:
                    st[0] -= 1
                cnt[t] += 1
    it = 0
    while st[0] > 0 and it < cap:
        if (it & 255) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(1, k)
        x = S[i]
        v = rng.randrange(1, m)
        if v in S:
            it += 1
            continue
        others = S[:i] + S[i + 1:]
        before = st[0]
        _apply(cnt, st, m, x, others, -1)
        _apply(cnt, st, m, v, others, 1)
        delta = st[0] - before
        T = 0.8 * (1 - it / cap) + 0.03
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = v
        else:
            _apply(cnt, st, m, v, others, -1)
            _apply(cnt, st, m, x, others, 1)
        it += 1
    return st[0] == 0


def _haar_search(k, deadline, rng):
    """Find the largest m with a k-set S in Z_m whose difference set covers Z_m (Haar graph has diameter 3).

    Returns (m, S) or None. Upper limit m <= k(k-1)+1 by counting.
    """
    m_max = k * (k - 1) + 1
    m = max(k, min(2 * k, m_max))
    S = [0] + rng.sample(range(1, m), k - 1)
    cap = 40000
    best = None
    while m <= m_max and time.monotonic() < deadline:
        if _sa(S, m, cap, deadline, rng):
            best = (m, list(S))
            m += 1
            continue
        ok = False
        while not ok and time.monotonic() < deadline:
            S = [0] + rng.sample(range(1, m), k - 1)
            ok = _sa(S, m, cap, deadline, rng)
        if not ok:
            break
        best = (m, list(S))
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.7 * time_limit - 1.0)

    # Trivial cases.
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
    candidates = []

    # Safe fallback: K_{d,d} has diameter 2.
    candidates.append(lib.haar_graph(d, range(d)))

    pg = _pg_candidate(d, D)
    if pg is not None:
        candidates.append(pg)

    # Cyclic Haar graphs with difference-covering connection sets (diameter 3 exactly when S - S = Z_m).
    if D == 3 and d >= 2 and (pg is None or pg[0] < lib.moore_bound(d, D)):
        found = _haar_search(d, deadline, rng)
        if found is not None:
            m, S = found
            candidates.append(lib.haar_graph(m, S))

    # Choose the largest candidate that passes the exact validity check.
    candidates.sort(key=lambda c: c[0], reverse=True)
    for n, edges in candidates:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return lib.haar_graph(d, range(d))
