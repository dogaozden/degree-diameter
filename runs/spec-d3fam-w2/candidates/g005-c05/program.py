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
# New construction: 2x2-base cyclic voltage lift.
#
# Base multigraph: A-vertices A0, A1 and B-vertices B0, B1, with
# multiplicities mult[i][j] of darts A_i -> B_j, where every row and column
# sums to d (so every base vertex has degree d). Each dart carries a voltage
# in Z_N, and the voltages on the same (i, j) pair are distinct, so the lift
# is simple, d-regular, bipartite, and has 4N vertices. Diameter 3 needs
# every pair of same-side vertices to share a neighbour, which bounds
# N by C(d, 2). Diameter-3 lifts of this shape can exceed Haar graphs
# (order 2N) because they have 4N vertices. We search voltages by annealing
# on the number of pairs at distance > 3.
# ----------------------------------------------------------------------------

def _lift_cost(N, V):
    """Return (bad pair count, n, edges) for the 2x2-base lift with voltage sets V."""
    darts = [(i, 2 + j, g) for i in range(2) for j in range(2) for g in V[i][j]]
    n, edges = lib.voltage_lift(4, darts, N)
    return lib.bad_pairs(n, edges, 3), n, edges


def _two_lift_search(d, N, rng, deadline):
    """Anneal voltages of the 2x2-base lift over Z_N; return (n, edges) with diameter <= 3, or None."""
    k = d // 2
    mult = [[k, d - k], [d - k, k]]
    while time.monotonic() < deadline:
        V = [[rng.sample(range(N), mult[i][j]) for j in range(2)] for i in range(2)]
        bad = _lift_cost(N, V)[0]
        steps = 3000
        for it in range(steps):
            if bad == 0:
                break
            if time.monotonic() >= deadline:
                break
            T = 0.05 + 1.0 * (1.0 - it / steps)
            i = rng.randrange(2)
            j = rng.randrange(2)
            if mult[i][j] == 0:
                continue
            t = rng.randrange(mult[i][j])
            x = rng.randrange(N)
            if x in V[i][j]:
                continue
            old = V[i][j][t]
            V[i][j][t] = x
            c = _lift_cost(N, V)[0]
            if c <= bad or rng.random() < math.exp(-(c - bad) / T):
                bad = c
            else:
                V[i][j][t] = old
        if bad == 0:
            _, n, edges = _lift_cost(N, V)
            return n, edges
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

    # Phase A: difference-cover Haar lifts (order 2N, needs S S^{-1} = G, |S| = d).
    haar_deadline = start + 0.4 * (deadline - start)
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= haar_deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, haar_deadline - time.monotonic())
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
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
        consider(n, edges)

    # Phase B: 2x2-base voltage lifts with 4N vertices. Ascend in N from the
    # smallest order that beats the current best; stop at the first failure.
    N_lo = best_n // 4 + 1
    N_hi = d * (d - 1) // 2
    for N in range(max(N_lo, 2), N_hi + 1):
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        sub = now + 0.4 * remaining
        res = _two_lift_search(d, N, rng, sub)
        if res is None:
            break
        consider(*res)

    return best
