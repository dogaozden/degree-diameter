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


def _tabu_cover(N, R, mul, inv, d, rng, steps, e):
    """Focused min-conflicts search for S (|S| = d) with S S^{-1} = G.

    Each move picks a random uncovered element g and a random s in S, then proposes
    x = g*s or x = g^{-1}*s. That x covers g together with s, so the move always
    makes progress on g. It replaces another index of S and is accepted by a
    Metropolis rule. A short tabu list stops immediate reversals.
    Returns S or None.
    """
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
    tabu = {}
    for it in range(steps):
        uncs = [g for g in range(N) if cnt[g] == 0]
        if not uncs:
            return S
        g = rng.choice(uncs)
        j = rng.randrange(d)
        b = S[j]
        if rng.random() < 0.5:
            x = mul(g, b)
        else:
            x = mul(inv(g), b)
        if x in S or tabu.get(x, -1) > it:
            continue
        i = rng.randrange(d - 1)
        if i >= j:
            i += 1
        old = S[i]
        delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / 0.5):
            S[i] = x
            unc += delta
            tabu[old] = it + 7
            if unc == 0:
                return S
        else:
            _upd(cnt, R, S, i, x, -1)
            _upd(cnt, R, S, i, old, +1)
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

    # Difference-cover Haar lifts: order 2N needs S S^{-1} = G with |S| = d.
    # Search N in DESCENDING order so the first success is the largest order.
    # Each N gets an equal share of the remaining time.
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    Ns = list(range(hi, max(lo, d) - 1, -1))
    for k, N in enumerate(Ns):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(Ns) - k)
        t_end = now + share
        groups = _group_list(N, rng)
        tabs = {}
        found = None
        while found is None and time.monotonic() < t_end:
            for idx, (_, mul, inv) in enumerate(groups):
                if time.monotonic() >= t_end:
                    break
                if idx not in tabs:
                    tabs[idx] = _ratio_table(N, mul, inv)
                R = tabs[idx]
                S = _tabu_cover(N, R, mul, inv, d, rng, 4000, R[0][0])
                if S is not None:
                    found = (S, mul)
                    break
        if found is not None:
            S, mul = found
            consider(*lib.group_lift(2, [(0, 1, g) for g in S], N, mul))
            break

    return best
