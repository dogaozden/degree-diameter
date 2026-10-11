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


def _mul_table(N, mul):
    """T[x][g] = x * g for group elements coded 0..N-1 (identity is 0)."""
    return [[mul(x, g) for g in range(N)] for x in range(N)]


# ---------------------------------------------------------------------------
# NEW: four-orbit group lift.
#
# Base graph: two "A" vertices A0, A1 and two "B" vertices B0, B1, with
# multiplicities m = [[k, d-k], [d-k, k]].  For each base pair (i, j) choose
# m_ij distinct group elements S[i][j].  The lift has vertices a_{i,x} and
# b_{j,y} (x, y in G), and a_{i,x} ~ b_{j, x*g} for g in S[i][j].
#
# Every vertex has degree d and the graph is bipartite (A side vs B side).
# Left multiplication by h is an automorphism, so the four vertices
# a_{0,e}, a_{1,e}, b_{0,e}, b_{1,e} represent all vertices up to symmetry.
# Diameter <= 3 therefore reduces to four breadth-first searches of depth 3.
# This gives order 4N, so it can beat the 2N Haar lifts at the same degree.
# ---------------------------------------------------------------------------

def _orbit_adj(N, T, S):
    """Adjacency lists of the four-orbit lift for voltage sets S."""
    adj = [[] for _ in range(4 * N)]
    for i in range(2):
        for j in range(2):
            for g in S[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = (2 + j) * N + T[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    return adj


def _orbit_missing(adj, total, reps):
    """Number of (representative, vertex) pairs at distance > 3, summed over representatives."""
    tot = 0
    for s in reps:
        seen = {s}
        frontier = [s]
        for _ in range(3):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if v not in seen:
                        seen.add(v)
                        nxt.append(v)
            frontier = nxt
        tot += total - len(seen)
    return tot


def _anneal_orbit(N, T, d, k, rng, t_end):
    """Anneal voltage sets for multiplicities [[k, d-k], [d-k, k]]; return S or None."""
    m = [[k, d - k], [d - k, k]]
    S = [[rng.sample(range(N), m[i][j]) for j in range(2)] for i in range(2)]
    total = 4 * N
    reps = (0, N, 2 * N, 3 * N)
    cur = _orbit_missing(_orbit_adj(N, T, S), total, reps)
    if cur == 0:
        return S
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while True:
        now = time.monotonic()
        if now >= t_end:
            return None
        temp = 1.5 * max(0.0, 1.0 - (now - t0) / span) + 0.02
        i = rng.randrange(2)
        j = rng.randrange(2)
        lst = S[i][j]
        pos = rng.randrange(len(lst))
        x = rng.randrange(N)
        if x in lst:
            continue
        old = lst[pos]
        lst[pos] = x
        new = _orbit_missing(_orbit_adj(N, T, S), total, reps)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
            if cur == 0:
                return S
        else:
            lst[pos] = old


def _orbit_edges(N, T, S):
    """Edge list of the four-orbit lift (order 4N)."""
    edges = []
    for i in range(2):
        for j in range(2):
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, (2 + j) * N + T[x][g]))
    return 4 * N, edges


def _orbit_search(d, D, best_n, t_end, rng):
    """Search four-orbit lifts with order 4N > best_n; return a valid (n, edges) or None."""
    lo = max(best_n // 4 + 1, d)
    hi = lib.moore_bound(d, 3) // 4
    found = None
    N = lo
    while N <= hi and time.monotonic() < t_end:
        groups = _group_list(N, rng)
        tables = [_mul_table(N, g[1]) for g in groups]
        combos = [(gi, k) for gi in range(len(groups)) for k in range(1, d)]
        rng.shuffle(combos)
        now = time.monotonic()
        slot_end = now + 0.5 * (t_end - now)
        result = None
        attempt = 0
        while result is None and time.monotonic() < slot_end:
            gi, k = combos[attempt % len(combos)]
            attempt += 1
            chunk_end = min(slot_end, time.monotonic() + 2.0)
            S = _anneal_orbit(N, tables[gi], d, k, rng, chunk_end)
            if S is not None:
                result = (gi, S)
        if result is None:
            break
        gi, S = result
        n, edges = _orbit_edges(N, tables[gi], S)
        if lib.is_valid(n, edges, d, D):
            found = (n, edges)
            N += 1
        else:
            break
    return found


# ---------------------------------------------------------------------------
# Difference-cover Haar lifts (from the parent program).
# ---------------------------------------------------------------------------

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

    # New: four-orbit group lifts, order 4N, searched first with most of the budget.
    try:
        res = _orbit_search(d, D, best_n, start + 0.7 * total, rng)
        if res is not None:
            consider(*res)
    except Exception:
        pass

    # Difference-cover Haar lifts with the remaining time: order 2N.
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, deadline - time.monotonic())
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

    return best
