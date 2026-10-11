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


# ---------------------------------------------------------------------------
# Bold stage: voltage lifts with k base vertices per side (k >= 3).
# Unlike the 2-vertex Haar lift (which needs S S^{-1} = G), a k-vertex base
# spreads the same-side distance-2 requirement over several orbits, so the
# lift order can exceed 2*(d^2-d+1)-style limits of the Haar construction.
# Search voltages directly, minimising the number of pairs at too large distance.
# ---------------------------------------------------------------------------

def _circulant_multiplicity(k, d):
    """k x k nonnegative integer matrix with all row and column sums equal to d."""
    q, r = divmod(d, k)
    return [[q + (1 if (j - i) % k < r else 0) for j in range(k)] for i in range(k)]


def _lift_adj(k, N, mt, volt):
    """Adjacency lists of the voltage lift. A_i = i*N + x, B_j = (k+j)*N + x."""
    n = 2 * k * N
    adj = [[] for _ in range(n)]
    for i in range(k):
        A = i * N
        for j in range(k):
            B = (k + j) * N
            for v in volt[i][j]:
                for x in range(N):
                    a = A + x
                    b = B + mt[x][v]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _cost(adj, n, half):
    """Number of (ordered) pairs violating: same-side distance > 2 or cross-side distance > 3."""
    r1 = [0] * n
    for v in range(n):
        m = 1 << v
        for u in adj[v]:
            m |= 1 << u
        r1[v] = m
    r2 = [0] * n
    for v in range(n):
        m = 0
        for u in adj[v]:
            m |= r1[u]
        r2[v] = m
    r3 = [0] * n
    for v in range(n):
        m = 0
        for u in adj[v]:
            m |= r2[u]
        r3[v] = m
    MA = (1 << half) - 1
    MB = ((1 << n) - 1) ^ MA
    bad = 0
    for v in range(n):
        if v < half:
            bad += (MA & ~r2[v]).bit_count() + (MB & ~r3[v]).bit_count()
        else:
            bad += (MB & ~r2[v]).bit_count() + (MA & ~r3[v]).bit_count()
    return bad


def _anneal_lift(k, N, mt, M, rng, deadline):
    """Search distinct voltages per base dart-bundle; return volt (k x k lists) or None."""
    n = 2 * k * N
    half = k * N
    pairs = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    volt = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            volt[i][j] = rng.sample(range(N), M[i][j])
    cur = _cost(_lift_adj(k, N, mt, volt), n, half)
    if cur == 0:
        return volt
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / span
        T = 0.6 * (1.0 - frac) + 0.05
        i, j = rng.choice(pairs)
        lst = volt[i][j]
        t = rng.randrange(len(lst))
        new = rng.randrange(N)
        if new in lst:
            continue
        old = lst[t]
        lst[t] = new
        c = _cost(_lift_adj(k, N, mt, volt), n, half)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if cur == 0:
                return volt
        else:
            lst[t] = old


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + budget
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

    # Stage 1: difference-cover (2-vertex Haar) lifts, given a share of the time.
    parent_deadline = start + 0.45 * budget
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    try:
        for N in range(lo, hi + 1):
            if time.monotonic() >= parent_deadline:
                break
            if 2 * N <= best_n:
                continue
            groups = _group_list(N, rng)
            tables = [None] * len(groups)
            found = None
            now = time.monotonic()
            deadline_N = now + 0.5 * max(0.0, parent_deadline - now)
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
    except Exception:
        pass

    # Stage 2 (bold): k-vertex-per-side voltage lifts, aiming above the current best.
    try:
        moore = lib.moore_bound(d, D)
        cands = []
        for k in range(3, 7):
            if k > d:
                continue
            M = _circulant_multiplicity(k, d)
            mx = max(max(row) for row in M)
            for N in range(max(mx, 2), moore // (2 * k) + 2):
                n = 2 * k * N
                if n > moore:
                    break
                if n > best_n:
                    cands.append((n, k, N, M))
        cands.sort(key=lambda c: c[0])
        for n, k, N, M in cands:
            if n <= best_n:
                continue
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 1.0:
                break
            attempt_end = now + max(2.0, 0.4 * remaining)
            attempt_end = min(attempt_end, deadline)
            groups = _group_list(N, rng)
            mul = rng.choice(groups)[1]
            mt = [[mul(x, v) for v in range(N)] for x in range(N)]
            volt = _anneal_lift(k, N, mt, M, rng, attempt_end)
            if volt is not None:
                darts = [(i, k + j, v) for i in range(k) for j in range(k) for v in volt[i][j]]
                try:
                    n2, e2 = lib.group_lift(2 * k, darts, N, mul)
                    consider(n2, e2)
                except Exception:
                    pass
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
