import math
import random
import time

import lib


def _set_contrib(cnt, S, idx, m, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered-difference contributions of S[idx] against every other element.

    Returns the change in the number of uncovered nonzero residues.
    """
    delta = 0
    v = S[idx]
    for j, s in enumerate(S):
        if j == idx:
            continue
        for z in ((v - s) % m, (s - v) % m):
            if sign > 0:
                if cnt[z] == 0:
                    delta -= 1
                cnt[z] += 1
            else:
                cnt[z] -= 1
                if cnt[z] == 0:
                    delta += 1
    return delta


def _cover_search(m, k, rng, deadline):
    """Find k distinct residues S in Z_m with S - S covering all of Z_m (a difference cover), or None.

    Simulated annealing on the number of uncovered nonzero differences. A difference cover S gives
    the Haar graph H(m, S) of order 2m and degree k with diameter <= 3.
    """
    if k > m:
        return None
    S = rng.sample(range(m), k)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    T = 0.3
    it = 0
    while unc > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() >= deadline:
            return None
        idx = rng.randrange(k)
        r = rng.randrange(m)
        if inS[r]:
            continue
        old = S[idx]
        d1 = _set_contrib(cnt, S, idx, m, -1)
        S[idx] = r
        d2 = _set_contrib(cnt, S, idx, m, +1)
        new = unc + d1 + d2
        if new <= unc or rng.random() < math.exp((unc - new) / T):
            inS[old] = False
            inS[r] = True
            unc = new
        else:
            _set_contrib(cnt, S, idx, m, -1)
            S[idx] = old
            _set_contrib(cnt, S, idx, m, +1)
    return sorted(S)


def _cover_graph(d, start_m, rng, deadline):
    """Grow m upward from start_m, keeping the largest verified difference-cover Haar graph of degree d."""
    best = None
    m = max(start_m, d)
    m_max = d * d - d + 1          # a difference cover of size d can cover at most d(d-1)+1 residues
    while m <= m_max and time.monotonic() < deadline:
        now = time.monotonic()
        slice_end = min(deadline, now + max(0.5, 0.4 * (deadline - now)))
        S = _cover_search(m, d, rng, slice_end)
        if S is None:
            S = _cover_search(m, d, rng, deadline)
        if S is None:
            break
        n, edges = lib.haar_graph(m, S)
        if not lib.is_valid(n, edges, d, 3):
            break
        best = (n, edges)
        m += 1
    return best


def _random_haar(d, D, rng, deadline):
    """Fallback for other diameters: random Haar graphs with growing m."""
    best = lib.haar_graph(d, range(d))
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
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 0:
        return 1, []

    best = None
    try:
        if D == 3:
            # Projective plane incidence graph is Moore-optimal when d-1 is a prime power.
            q = d - 1
            if q >= 2 and lib.is_prime_power(q):
                cand = lib.projective_plane_incidence(q)
                if lib.is_valid(cand[0], cand[1], d, D):
                    return cand

            # Araujo-Pardo / Lopez record base when d-2 is a prime power >= 3.
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                try:
                    cand = lib.araujo_lopez_graph(d - 2)
                    if lib.is_valid(cand[0], cand[1], d, D):
                        best = cand
                except Exception:
                    best = None

            # Different construction: cyclic Haar graphs H(m, S) where S is a difference cover of Z_m.
            # Such graphs have diameter 3 and degree d, and this search can go beyond the base order.
            start_m = best[0] // 2 + 1 if best else d
            try:
                cov = _cover_graph(d, start_m, rng, deadline)
                if cov is not None and (best is None or cov[0] > best[0]):
                    best = cov
            except Exception:
                pass
        else:
            best = _random_haar(d, D, rng, deadline)
    except Exception:
        best = None

    if best is None or not lib.is_valid(best[0], best[1], d, D):
        try:
            cand = lib.haar_graph(d, range(d))  # K_{d,d}
            if lib.is_valid(cand[0], cand[1], d, D):
                return cand
        except Exception:
            pass
        return 1, []
    return best
