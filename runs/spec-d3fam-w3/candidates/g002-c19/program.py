import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Difference-cover Haar graphs (diameter 3, valid for any D >= 3).
#
# For S a d-subset of Z_m with 0 in S and S - S = Z_m, the Haar graph
#   a_x ~ b_y  iff  y - x in S
# is d-regular, bipartite, and has diameter <= 3. Since 0 is in S, (S - S) + S
# contains S - S = Z_m, which covers the a-b distances.
# ----------------------------------------------------------------------------

def _cover_search(m, d, rng, deadline, iters):
    """Anneal a d-subset S of Z_m (with 0 in S) so that S - S covers all of Z_m. Returns S or None."""
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    exp = math.exp
    rand = rng.random

    for it in range(iters):
        if zeros == 0:
            return S
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        T = 0.8 * (0.05 / 0.8) ** (it / iters)
        idx = rng.randrange(1, d)
        old = S[idx]
        new = rng.randrange(1, m)
        if inS[new]:
            continue

        # Remove the differences involving `old`.
        pold = []
        for j in range(d):
            if j != idx:
                t = S[j]
                pold.append((old - t) % m)
                pold.append((t - old) % m)
        z = zeros
        for x in pold:
            cnt[x] -= 1
            if cnt[x] == 0:
                z += 1

        # Add the differences involving `new`.
        S[idx] = new
        pnew = []
        for j in range(d):
            if j != idx:
                t = S[j]
                pnew.append((new - t) % m)
                pnew.append((t - new) % m)
        for x in pnew:
            if cnt[x] == 0:
                z -= 1
            cnt[x] += 1

        delta = z - zeros
        if delta <= 0 or rand() < exp(-delta / T):
            zeros = z
            inS[old] = False
            inS[new] = True
        else:
            for x in pnew:
                cnt[x] -= 1
            for x in pold:
                cnt[x] += 1
            S[idx] = old

    return S if zeros == 0 else None


def _haar_search(d, m_start, deadline, rng, consider):
    """Search difference covers for m = m_start, m_start+1, ... and offer each Haar graph (order 2m)."""
    m = m_start
    m_max = d * (d - 1) + 1
    while m <= m_max and time.monotonic() < deadline:
        S = None
        while time.monotonic() < deadline:
            S = _cover_search(m, d, rng, deadline, 150000)
            if S is not None:
                break
        if S is None:
            break
        n, e = lib.haar_graph(m, S)
        consider(n, e)
        m += 1


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph.
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            try:
                consider(*lib.projective_plane_incidence(d - 1))
            except (ValueError, StopIteration, KeyError):
                pass
            if lib.is_valid(best[0], best[1], d, D):
                return best

    # Araujo-Pardo & Lopez record family (diameter 3), used as the base to beat.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except (ValueError, StopIteration, KeyError):
            pass

    # Main search: difference-cover Haar graphs above the current best half-order,
    # so every success is a strict improvement.
    m_start = max(d, best_n // 2 + 1)
    if m_start <= d * (d - 1) + 1:
        _haar_search(d, m_start, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            return 1, []
    return best
