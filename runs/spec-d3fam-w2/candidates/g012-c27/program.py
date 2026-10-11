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


# ---------------------------------------------------------------- new construction
# Two-orbit cyclic bi-lift. Base graph: A0, A1 | B0, B1 with dart multiplicities
# M = [[a, d-a], [d-a, a]] (every base vertex has total degree d). Voltages are
# distinct elements of Z_N per base pair, so the lift is simple and d-regular on
# 4N vertices. Voltages are annealed to minimise the number of pairs at distance > 3.

def _multi_edges(N, volt):
    """Lift of the two-orbit base graph: A_i -> B_j with voltage g joins A_i,x to B_j,(x+g)."""
    edges = []
    for i in range(2):
        for j in range(2):
            for g in volt[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + (x + g) % N))
    return edges


def _anneal_multi(d, N, a, rng, deadline, steps):
    """Anneal voltages so the 4N-vertex lift has diameter 3; return voltages or None."""
    M = [[a, d - a], [d - a, a]]
    volt = [[rng.sample(range(N), M[i][j]) for j in range(2)] for i in range(2)]
    cur = lib.bad_pairs(4 * N, _multi_edges(N, volt), 3)
    cells = [(i, j) for i in range(2) for j in range(2)]
    for it in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i, j = rng.choice(cells)
        idx = rng.randrange(M[i][j])
        x = rng.randrange(N)
        if x in volt[i][j]:
            continue
        old = volt[i][j][idx]
        volt[i][j][idx] = x
        new = lib.bad_pairs(4 * N, _multi_edges(N, volt), 3)
        T = 1.5 * (1.0 - it / steps) + 0.05
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            volt[i][j][idx] = old
    return volt if cur == 0 else None


def _multi_search(d, best, deadline, rng):
    """Ascend N from best_n // 4 + 1 while two-orbit lifts keep succeeding."""
    N = best[0] // 4 + 1
    while time.monotonic() < deadline:
        found = None
        while found is None and time.monotonic() < deadline:
            a = rng.randint(1, d - 1)
            found = _anneal_multi(d, N, a, rng, deadline, 1500)
        if found is None:
            break
        n, e = 4 * N, _multi_edges(N, found)
        if n > best[0] and lib.is_valid(n, e, d, 3):
            best = (n, e)
        N += 1
    return best


# ---------------------------------------------------------------- parent search

def _difference_search(d, best, deadline, rng):
    """Difference-cover group lifts with 2 base vertices (parent construction)."""
    best_n = best[0]
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
            if n > best[0] and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_n = n
        except Exception:
            pass
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    # Phase 1: difference-cover search (parent construction), limited share of time.
    best = _difference_search(d, best, start + 0.35 * total, rng)

    # Phase 2: two-orbit voltage annealing (new construction), uses the rest.
    best = _multi_search(d, best, start + total, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
