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


# ----------------------------------------------------------------------------
# New construction: Z_N voltage lifts of a 4-vertex base graph
# (A = {0, 1}, B = {2, 3}, multiplicity matrix [[x, d-x], [d-x, x]]).
# Every vertex of the lift has degree d. Because the lift is fibre-transitive,
# diameter <= 3 holds iff every base vertex s, taken as source (s, 0), reaches
# all 4N vertices within 3 steps. Reachability is tracked as N-bit masks.
# ----------------------------------------------------------------------------

def _rot(m, g, N, full):
    """Cyclic shift of an N-bit mask by g: position x goes to x + g mod N."""
    if g == 0:
        return m
    return ((m << g) | (m >> (N - g))) & full


def _walk_cost(N, darts):
    """Number of (source, target) pairs NOT within distance 3, over the 4 base sources."""
    full = (1 << N) - 1
    total = 0
    for s in range(4):
        F = [0, 0, 0, 0]
        F[s] = 1
        R = [0, 0, 0, 0]
        R[s] = 1
        for _ in range(3):
            NF = [0, 0, 0, 0]
            for a, b, g in darts:
                fa = F[a]
                if fa:
                    NF[b] |= _rot(fa, g, N, full)
                fb = F[b]
                if fb:
                    NF[a] |= _rot(fb, (N - g) % N, N, full)
            F = NF
            R[0] |= F[0]
            R[1] |= F[1]
            R[2] |= F[2]
            R[3] |= F[3]
        for v in range(4):
            total += N - R[v].bit_count()
    return total


def _search4(d, N, x, rng, deadline):
    """Anneal voltages for a 4-vertex base lift over Z_N with split x; return darts or None."""
    pairs = [(0, 2, x), (0, 3, d - x), (1, 2, d - x), (1, 3, x)]
    darts = []
    pidx = []
    used = []
    for pi, (a, b, m) in enumerate(pairs):
        gs = rng.sample(range(N), m)
        used.append(set(gs))
        for g in gs:
            darts.append([a, b, g])
            pidx.append(pi)
    cur = _walk_cost(N, darts)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    frac = 0.0
    it = 0
    while cur > 0:
        if (it & 63) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / span
        it += 1
        T = 0.05 + 1.0 * (1.0 - frac)
        i = rng.randrange(len(darts))
        pi = pidx[i]
        g = rng.randrange(N)
        if g in used[pi]:
            continue
        old = darts[i][2]
        darts[i][2] = g
        new = _walk_cost(N, darts)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            used[pi].discard(old)
            used[pi].add(g)
            cur = new
        else:
            darts[i][2] = old
    if cur == 0:
        return [(a, b, g) for a, b, g in darts]
    return None


def _four_search(d, best_n, rng, deadline, consider):
    """Search N upward from just below the current record order divided by 4."""
    N = max(d, best_n // 4 - 3)
    xs = list(range(1, d // 2 + 1))
    while time.monotonic() < deadline:
        now = time.monotonic()
        slice_end = now + max(1.0, 0.5 * (deadline - now))
        found = None
        while found is None and time.monotonic() < slice_end:
            x = rng.choice(xs)
            attempt_end = min(slice_end, time.monotonic() + 4.0)
            found = _search4(d, N, x, rng, attempt_end)
        if found is None:
            break
        try:
            n, edges = lib.voltage_lift(4, found, N)
            consider(n, edges)
        except Exception:
            break
        N += 1


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

    # New bold construction: 4-vertex base voltage lifts over Z_N.
    if d >= 4:
        now = time.monotonic()
        four_deadline = now + 0.6 * max(0.0, deadline - now)
        try:
            _four_search(d, best_n, rng, four_deadline, consider)
        except Exception:
            pass

    # Difference-cover group lifts (2-vertex base): order 2N needs S S^{-1} = G with |S| = d.
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
                    tables[idx] = _ratio_table(N, mul, inv)
                R = tables[idx]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
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
