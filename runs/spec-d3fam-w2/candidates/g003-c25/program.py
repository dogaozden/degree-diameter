import math
import random
import time

import lib

_STEPS = 20000  # annealing steps per restart


def _fallback(d, D):
    """Verified baseline graphs for small or unsupported parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def _abelian(m, k):
    """Z_m x Z_k with element a*k+b; identity is 0."""
    def mul(x, y):
        a, b = divmod(x, k)
        c, e = divmod(y, k)
        return ((a + c) % m) * k + (b + e) % k

    def inv(x):
        a, b = divmod(x, k)
        return ((-a) % m) * k + (-b) % k

    return m * k, mul, inv


def _groups(N, rng, cap):
    """Cyclic group of order N first, then a random sample of non-cyclic abelian and semidirect groups."""
    divs = [k for k in range(2, N) if N % k == 0]
    cands = []
    for k in divs:
        m = N // k
        if 2 <= m <= k and math.gcd(m, k) > 1:
            cands.append(_abelian(m, k))
    for k in divs:
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            try:
                cands.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    rng.shuffle(cands)
    return [_abelian(N, 1)] + cands[: max(0, cap - 1)]


def _upd(cnt, R, S, skip, v, sign):
    """Add or remove the ordered differences of v against S[j] for j != skip.

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


def _anneal(N, mul, inv, d, rng, steps):
    """Generator: annealing for d elements S with S S^{-1} = G.

    Yields None periodically so the driver can round-robin groups, and yields
    the cover S once found. Restarts from a fresh random state when a run fails.
    """
    iv = [inv(y) for y in range(N)]
    R = [[mul(x, iv[y]) for y in range(N)] for x in range(N)]
    t_hi, t_lo = 1.0, 0.08
    ratio = (t_lo / t_hi) ** (1.0 / steps)
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        cnt[0] = 1  # identity is always covered
        for a in S:
            for b in S:
                if a != b:
                    cnt[R[a][b]] += 1
        unc = cnt.count(0)
        T = t_hi
        for it in range(steps):
            if unc == 0:
                break
            if (it & 511) == 0:
                yield None
            T *= ratio
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in inS:
                continue
            old = S[i]
            delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, 1)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[i] = x
                inS.discard(old)
                inS.add(x)
                unc += delta
            else:
                _upd(cnt, R, S, i, x, -1)
                _upd(cnt, R, S, i, old, 1)
        if unc == 0:
            yield list(S)
            return


def _search_N(N, d, rng, until):
    """Round-robin annealing over several groups of order N until time 'until'.

    Returns (mul, S) on success, or None.
    """
    groups = _groups(N, rng, 10)
    active = [(mul, _anneal(N, mul, inv, d, rng, _STEPS)) for _, mul, inv in groups]
    while active and time.monotonic() < until:
        keep = []
        for mul, gen in active:
            if time.monotonic() >= until:
                break
            try:
                res = next(gen)
            except StopIteration:
                continue
            if res is None:
                keep.append((mul, gen))
            else:
                return mul, res
        active = keep
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.5)
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

    # Only the diameter-3 regime is searched.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
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
    # Search N ascending; each N gets a share of the remaining time.
    lo = max(best_n // 2 + 1, d)
    hi = d * (d - 1) + 1
    N = lo
    while N <= hi and time.monotonic() < deadline:
        if 2 * N > best_n:
            now = time.monotonic()
            until = min(deadline, now + 0.3 * (deadline - now))
            res = _search_N(N, d, rng, until)
            if res is not None:
                mul, S = res
                try:
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
                    consider(n, edges)
                except Exception:
                    pass
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
