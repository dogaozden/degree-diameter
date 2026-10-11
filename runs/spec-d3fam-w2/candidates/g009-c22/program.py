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


def _anneal(N, R, d, rng, steps, e):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found."""
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


def _search_N(N, d, rng, until):
    """Repeated annealing over several groups of order N until time `until`.

    Returns (group_index, S, groups) on success, or None.
    """
    groups = _group_list(N, rng)
    tables = [None] * len(groups)
    while time.monotonic() < until:
        for idx in range(len(groups)):
            if time.monotonic() >= until:
                break
            if tables[idx] is None:
                tables[idx] = _ratio_table(N, groups[idx][1], groups[idx][2])
            R = tables[idx]
            S = _anneal(N, R, d, rng, 6000, R[0][0])
            if S is not None:
                return idx, S, groups
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(50.0, 0.8 * time_limit - 2.0)
    deadline = start + max(0.0, budget)
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

    # Difference-cover group lifts of order 2N with S S^{-1} = G, |S| = d.
    # Search N DESCENDING from the Moore-type limit: the first success is the
    # largest feasible N tried, so it is the best possible lift from this family.
    # Time is split evenly across the remaining N values.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    Ns = list(range(hi, lo - 1, -1))
    for i, N in enumerate(Ns):
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break
        if 2 * N <= best_n:
            break
        per = remaining / (len(Ns) - i)
        res = _search_N(N, d, rng, now + per)
        if res is not None:
            idx, S, groups = res
            try:
                n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, groups[idx][1])
                consider(n, edges)
            except Exception:
                pass
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
