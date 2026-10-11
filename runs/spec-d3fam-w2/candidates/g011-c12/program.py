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
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k of order N."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
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
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip.

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


def _tabu(N, R, M, invs, d, rng, until):
    """Tabu search for d elements S with S S^{-1} = G (a difference cover).

    New move rule (coverage-driven tabu): pick a random uncovered group element g and
    only consider replacements x that would create a difference equal to g, namely
    x = g*b or x = g^{-1}*b for some b in S. Each candidate is evaluated exactly against
    every position, the best non-tabu move is taken even when it worsens the cost, and
    recently removed elements are frozen for a few steps. Returns S, or None on timeout.
    """
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[0] = 1  # identity is covered by a = a
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    tabu_until = [0] * N
    step = 0
    while time.monotonic() < until:
        step += 1
        uncs = [g for g in range(N) if cnt[g] == 0]
        g = rng.choice(uncs)
        cands = set()
        ginv = invs[g]
        for b in S:
            cands.add(M[g][b])
            cands.add(M[ginv][b])
        best_i = -1
        best_x = -1
        bd = None
        for x in cands:
            if x in S or tabu_until[x] > step:
                continue
            for i in range(d):
                old = S[i]
                dl = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
                _upd(cnt, R, S, i, x, -1)
                _upd(cnt, R, S, i, old, +1)
                if bd is None or dl < bd or (dl == bd and rng.random() < 0.3):
                    bd = dl
                    best_i = i
                    best_x = x
        if bd is None:
            continue
        old = S[best_i]
        _upd(cnt, R, S, best_i, old, -1)
        _upd(cnt, R, S, best_i, best_x, +1)
        S[best_i] = best_x
        unc += bd
        if unc == 0:
            return S
        tabu_until[old] = step + 2 + rng.randrange(d)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

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

    # Difference-cover group lifts: order 2N needs S S^{-1} = G with |S| = d.
    # Failure at one N does not rule out N+1, so the scan continues past failures.
    # Each N gets a share of the remaining time, and each group is searched by tabu.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    Ns = list(range(lo, hi + 1))
    for k, N in enumerate(Ns):
        now = time.monotonic()
        if now >= deadline:
            break
        if 2 * N <= best_n:
            continue
        share = (deadline - now) / (len(Ns) - k)
        end_N = now + min(deadline - now, 1.5 * share)
        groups = _group_list(N, rng)
        prep = [None] * len(groups)
        found = None
        gi = 0
        while found is None:
            now = time.monotonic()
            if now >= end_N:
                break
            idx = gi % len(groups)
            gi += 1
            if prep[idx] is None:
                mul, inv = groups[idx][1], groups[idx][2]
                invs = [inv(x) for x in range(N)]
                R = _ratio_table(N, mul, inv)
                M = [[mul(x, y) for y in range(N)] for x in range(N)]
                prep[idx] = (R, M, invs)
            R, M, invs = prep[idx]
            S = _tabu(N, R, M, invs, d, rng, min(end_N, now + 0.6))
            if S is not None:
                found = (idx, S)
        if found is not None:
            idx, S = found
            mul = groups[idx][1]
            try:
                n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
                consider(n, edges)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
