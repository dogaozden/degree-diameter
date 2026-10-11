import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _group_list(N, rng):
    """Cyclic group of order N plus a random sample of semidirect products Z_m x| Z_k of order N."""
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
    for m, k, r in cands[:14]:
        try:
            groups.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered quotients of v against S[j], j != skip.

    Returns the change in the number of uncovered group elements.
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


def _anneal(N, R, d, rng, end, steps):
    """Find S of size d containing the identity 0 with S S^{-1} = G; None on failure or timeout.

    Right-multiplying S by a fixed element preserves S S^{-1}, so WLOG 0 is in S.
    """
    pool = list(range(1, N))
    S = [0] + rng.sample(pool, d - 1)
    cnt = [0] * N
    cnt[0] = 1
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        if (it & 255) == 0 and time.monotonic() >= end:
            return None
        T = 0.5 * (0.02 ** (it / steps))
        i = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[i]
        delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _upd(cnt, R, S, i, x, -1)
            _upd(cnt, R, S, i, old, +1)
    return None


def _find(N, d, rng, end):
    """Search group lifts of order N, rotating through groups and restarting. Returns (mul, S) or None."""
    groups = _group_list(N, rng)
    tables = {}
    rounds = 0
    while time.monotonic() < end:
        gi = rounds % len(groups)
        rounds += 1
        if gi not in tables:
            _, mul, inv = groups[gi]
            tables[gi] = _ratio_table(N, mul, inv)
        S = _anneal(N, tables[gi], d, rng, end, 20000)
        if S is not None:
            return groups[gi][1], S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 3.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    if D != 3 or d < 3:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Group lifts over 2 base vertices: order 2N needs S S^{-1} = G with |S| = d.
    # Search N ascending from the first value that could beat the current best.
    hi = d * (d - 1) + 1
    N = max(best_n // 2 + 1, d)
    while N <= hi and time.monotonic() < deadline:
        now = time.monotonic()
        end = now + 0.6 * (deadline - now)
        try:
            found = _find(N, d, rng, end)
        except Exception:
            found = None
        if found is None:
            break
        mul, S = found
        try:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, edges)
        except Exception:
            pass
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
