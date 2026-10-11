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


def _tables(N, mul, inv):
    """Return (MT, IV, R): full product table, inverse table, and R[x][y] = x * y^{-1}."""
    MT = [[mul(x, y) for y in range(N)] for x in range(N)]
    IV = [inv(y) for y in range(N)]
    R = [[MT[x][IV[y]] for y in range(N)] for x in range(N)]
    return MT, IV, R


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


def _anneal(N, R, d, rng, steps, e):
    """Find d distinct elements S with S S^{-1} = G by simulated annealing; None if not found."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[e] = 1
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        T = 1.0 - 0.95 * it / steps
        i = rng.randrange(d)
        x = rng.randrange(N)
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


def _swap(cnt, R, S, i, x):
    """Replace S[i] by x, keeping cnt (ordered differences plus identity) consistent.

    Returns the change in the number of uncovered elements.
    """
    old = S[i]
    ch = 0
    for j, b in enumerate(S):
        if j == i:
            continue
        for g in (R[old][b], R[b][old]):
            cnt[g] -= 1
            if cnt[g] == 0:
                ch += 1
    for j, b in enumerate(S):
        if j == i:
            continue
        for g in (R[x][b], R[b][x]):
            if cnt[g] == 0:
                ch -= 1
            cnt[g] += 1
    S[i] = x
    return ch


def _tabu(N, MT, IV, R, d, rng, iters, deadline):
    """Focused tabu search for S with S S^{-1} = G.

    Each move picks a random uncovered g and proposes x with x * s^{-1} = g or s * x^{-1} = g
    for some s in S, so every proposal covers g. The best non-tabu swap is applied.
    Returns S, or None if not found within iters steps or before the deadline.
    """
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[0] += 1  # identity
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    tabu_until = [-1] * d
    for it in range(iters):
        if (it & 127) == 0 and time.monotonic() >= deadline:
            return None
        uncovered = [g for g in range(N) if cnt[g] == 0]
        g = rng.choice(uncovered)
        gi = IV[g]
        best = None
        bestval = None
        for _ in range(2 * d):
            j = rng.randrange(d)
            b = S[j]
            x = MT[g][b] if rng.random() < 0.5 else MT[gi][b]
            if x in S:
                continue
            i = rng.randrange(d - 1)
            if i >= j:
                i += 1
            if tabu_until[i] > it:
                continue
            old = S[i]
            ch = _swap(cnt, R, S, i, x)
            _swap(cnt, R, S, i, old)
            val = unc + ch
            if bestval is None or val < bestval or (val == bestval and rng.random() < 0.5):
                bestval = val
                best = (i, x)
        if best is None:
            continue
        i, x = best
        unc += _swap(cnt, R, S, i, x)
        tabu_until[i] = it + rng.randint(2, 6)
        if unc == 0:
            return S
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
    # Search N ascending; every success raises best_n, so later N must beat it.
    # Each group alternates a focused tabu search with simulated annealing.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            break
        if 2 * N <= best_n:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, deadline - now)
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    mul, inv = groups[idx][1], groups[idx][2]
                    tables[idx] = _tables(N, mul, inv)
                MT, IV, R = tables[idx]
                S = _tabu(N, MT, IV, R, d, rng, 3000, deadline_N)
                if S is None and time.monotonic() < deadline_N:
                    S = _anneal(N, R, d, rng, 3000, 0)
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
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
