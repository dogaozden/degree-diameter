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
# New helper: two-base-vertex voltage lift over Z_N.
#
# Base graph: A0, A1 (one side) and B0, B1 (other side), all complete.
# Dart multiplicities are a, d-a, d-a, a so every base vertex has degree d.
# Each base pair (Ai, Bj) carries a set of distinct voltages in Z_N.
# The lift has 4N vertices, is bipartite by construction, and has max degree d.
# We anneal the voltages to minimise the number of pairs at distance > 3.
# ---------------------------------------------------------------------------

_KEYS = ((0, 0), (0, 1), (1, 0), (1, 1))


def _lift22_eval(N, V):
    """Build the 4N-vertex lift for voltage sets V and return (n, edges, bad_pairs)."""
    darts = [(i, 2 + j, g) for (i, j) in _KEYS for g in V[(i, j)]]
    n, edges = lib.group_lift(4, darts, N, lambda x, y: (x + y) % N)
    return n, edges, lib.bad_pairs(n, edges, 3)


def _two_base_search(d, N, rng, t_end):
    """Anneal voltages of the 2+2 base lift over Z_N until diameter 3; return edges or None."""
    a = rng.randint(1, d - 1)
    size = {(0, 0): a, (1, 1): a, (0, 1): d - a, (1, 0): d - a}
    V = {k: rng.sample(range(N), size[k]) for k in _KEYS}
    _, edges, cur = _lift22_eval(N, V)
    if cur == 0:
        return edges
    T = 0.5
    while time.monotonic() < t_end:
        k = rng.choice(_KEYS)
        idx = rng.randrange(len(V[k]))
        x = rng.randrange(N)
        if x in V[k]:
            continue
        old = V[k][idx]
        V[k][idx] = x
        _, edges, c = _lift22_eval(N, V)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if c == 0:
                return edges
        else:
            V[k][idx] = old
    return None


def _two_base_phase(d, best_n, moore, deadline, consider, rng):
    """Try 4N-vertex 2+2 lifts for N ascending; each success raises best_n."""
    for N in range(max(2, best_n // 4 + 1), moore // 4 + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        if 4 * N <= best_n:
            continue
        budget = max(2.0, 0.4 * (deadline - now))
        t_end = min(deadline, now + budget)
        try:
            edges = _two_base_search(d, N, rng, t_end)
        except Exception:
            edges = None
        if edges is not None:
            consider(4 * N, edges)


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

    moore = lib.moore_bound(d, 3)

    # Phase 1 (new): 2+2 voltage lifts over Z_N, order 4N.
    phase1_end = start + 0.4 * (deadline - start)
    _two_base_phase(d, best_n, moore, phase1_end, consider, rng)

    # Phase 2: difference-cover group lifts, order 2N with S S^{-1} = G, |S| = d.
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
