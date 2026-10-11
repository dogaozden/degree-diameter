import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Combined construction.
#
# 1. Moore-extremal case: incidence graph of PG(2, d-1) when d-1 is a prime power.
# 2. Araujo-Pardo & Lopez record family for d = q + 2, q a prime power.
# 3. Bi-Cayley graphs over groups G of order N: vertices a_x, b_x (x in G),
#    a_x ~ b_{x s} for s in S, |S| = d. Degrees are exactly d, the graph is
#    bipartite, and diameter <= 3 holds when S S^{-1} = G. This gives order 2N
#    with N <= d(d-1)+1. We search N upward from the current record, using
#    simulated annealing over S on the cyclic group and several semidirect
#    products of order N.
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2), or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _group_list(N, rng, cap=6):
    """Cyclic group of order N plus a sample of semidirect products Z_m x| Z_k of order N."""
    groups = [lib.cyclic_group(N)]
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    for m, k, r in cands[:cap]:
        try:
            groups.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return groups


def _tables(N, grp):
    """Return (M, R): M[x][y] = x*y and R[x][y] = x*y^{-1}. Identity is element 0."""
    _, mul, inv = grp
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(y) for y in range(N)]
    R = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, R


def _cover(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) the differences created by v against S[j], j != skip.

    Returns the change in the number of uncovered non-identity elements.
    """
    ch = 0
    Rv = R[v]
    for j, b in enumerate(S):
        if j == skip:
            continue
        for g in (Rv[b], R[b][v]):
            if sign > 0:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
    return ch


def _anneal(N, R, d, rng, steps, deadline):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found in time."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[0] = 1  # identity is always covered
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt[1:] if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        if (it & 2047) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.6 * (0.02 ** (it / steps))
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        delta = _cover(cnt, R, S, i, old, -1) + _cover(cnt, R, S, i, x, 1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _cover(cnt, R, S, i, x, -1)
            _cover(cnt, R, S, i, old, 1)
    return None


def _search(N, d, rng, deadline):
    """Search for a valid S in some group of order N before the deadline. Returns (S, M) or None."""
    groups = _group_list(N, rng)
    tabs = [None] * len(groups)
    failed = [False] * len(groups)
    while time.monotonic() < deadline:
        progressed = False
        for idx in range(len(groups)):
            if time.monotonic() >= deadline:
                break
            if failed[idx]:
                continue
            if tabs[idx] is None:
                try:
                    tabs[idx] = _tables(N, groups[idx])
                except Exception:
                    failed[idx] = True
                    continue
            M, R = tabs[idx]
            progressed = True
            S = _anneal(N, R, d, rng, 20000, deadline)
            if S is not None:
                return S, M
        if not progressed:
            break
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D != 3 or d < 3:
        return best

    try:
        # Moore-extremal case: incidence graph of PG(2, d-1).
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best

        # Araujo-Pardo & Lopez record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

        # Bi-Cayley search: order 2N needs S S^{-1} = G with |S| = d.
        # Only N with 2N > best_n can improve; search ascending from the smallest.
        hi = d * (d - 1) + 1
        lo = max(d, best_n // 2 + 1)
        for N in range(lo, hi + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            budget = 0.6 * (deadline - now)
            res = _search(N, d, rng, now + budget)
            if res is None:
                break
            S, M = res
            edges = [(x, N + M[x][s]) for x in range(N) for s in S]
            consider(2 * N, edges)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
