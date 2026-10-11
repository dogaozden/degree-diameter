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


# ---- Voltage lifts over a 2k-vertex bipartite base (k vertices per side) ----

def _block_matrix(k, d):
    """Dart counts M[i][j] from side-A vertex i to side-B vertex j; every row and column sums to d."""
    q, r = divmod(d, k)
    return [[q + (1 if (j - i) % k < r else 0) for j in range(k)] for i in range(k)]


def _lift(k, blocks, N, mul):
    """Lift the base graph: A_i = base i, B_j = base k+j, darts (i, k+j, g)."""
    darts = [(i, k + j, g) for (i, j), gs in blocks.items() for g in gs]
    return lib.group_lift(2 * k, darts, N, mul)


def _voltage_search(k, d, N, mul, rng, deadline):
    """Anneal voltages on a fixed block-matrix base until the lift has diameter <= 3.

    Returns (n, edges) on success, None on timeout. Degree is exactly d on every vertex
    because the voltages inside each block are distinct.
    """
    M = _block_matrix(k, d)
    if max(max(row) for row in M) > N:
        return None
    blocks = {}
    for i in range(k):
        for j in range(k):
            if M[i][j]:
                blocks[(i, j)] = rng.sample(range(N), M[i][j])
    keys = list(blocks)
    n, edges = _lift(k, blocks, N, mul)
    cost = lib.bad_pairs(n, edges, 3)
    while cost > 0:
        if time.monotonic() >= deadline:
            return None
        key = keys[rng.randrange(len(keys))]
        gs = blocks[key]
        t = rng.randrange(len(gs))
        x = rng.randrange(N)
        if x in gs:
            continue
        old = gs[t]
        gs[t] = x
        n2, e2 = _lift(k, blocks, N, mul)
        c2 = lib.bad_pairs(n2, e2, 3)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / 0.5):
            cost = c2
            n, edges = n2, e2
        else:
            gs[t] = old
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
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

    # Phase 1: difference-cover lifts (2-vertex base), short budget.
    phase1_end = start + 0.2 * total
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= phase1_end:
            break
        if 2 * N <= best_n:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, phase1_end - now)
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

    # Phase 2: voltage lifts over 2k-vertex bases (k = 2, 3, 4), aiming above best_n.
    moore = lib.moore_bound(d, D)
    ks = (2, 3, 4)
    slice_s = max(1.5, 0.08 * total)
    while time.monotonic() < deadline:
        tried = False
        for k in ks:
            if time.monotonic() >= deadline:
                break
            lo_k = best_n // (2 * k) + 1
            hi_k = min(moore // (2 * k), lo_k + 8)
            if lo_k > hi_k:
                continue
            tried = True
            N = rng.randint(lo_k, hi_k)
            groups = _group_list(N, rng)
            mul = groups[rng.randrange(len(groups))][1]
            end = min(deadline, time.monotonic() + slice_s)
            try:
                res = _voltage_search(k, d, N, mul, rng, end)
            except Exception:
                res = None
            if res is not None:
                consider(*res)
        if not tried:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
