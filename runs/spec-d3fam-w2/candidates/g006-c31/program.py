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
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip."""
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
# New helper: orbit-lift search for diameter 3 with k orbits per side.
#
# The graph is a Z-lift over a group G of order N with k "A" base vertices and
# k "B" base vertices. Dart (i, j, g) joins A-vertex (i, x) to B-vertex (j, x*g).
# Left multiplication by G is an automorphism, so every vertex is equivalent to
# (orbit, identity). Hence diameter <= 3 holds iff all 2k representatives
# (orbit, e) reach every vertex within 3 steps. The cost is the total number of
# unreached (representative, vertex) pairs, minimised by simulated annealing
# over the voltages. Base multigraph: c = sum of d random permutation matrices,
# so every base vertex has degree exactly d.
# ---------------------------------------------------------------------------

def _random_counts(k, d, rng):
    """k x k nonnegative integer matrix with all row and column sums equal to d."""
    c = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            c[i][p[i]] += 1
    return c


def _orbit_cost(N, k, volt, M):
    """Number of unreached (representative, vertex) pairs within distance 3."""
    V = 2 * k * N
    adj = [[] for _ in range(V)]
    for i in range(k):
        ai = i * N
        for j in range(k):
            bj = (k + j) * N
            for g in volt[i][j]:
                for x in range(N):
                    a = ai + x
                    b = bj + M[x][g]
                    adj[a].append(b)
                    adj[b].append(a)
    total = 0
    for r in range(2 * k):
        src = r * N
        seen = {src}
        frontier = [src]
        for _ in range(3):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            frontier = nxt
        total += V - len(seen)
    return total


def _search_orbit(N, k, d, groups, rng, deadline, steps):
    """Simulated annealing with restarts. Returns (group, volt) or None."""
    tables = {}
    while time.monotonic() < deadline:
        gi = rng.randrange(len(groups))
        group = groups[gi]
        if gi not in tables:
            mul = group[1]
            tables[gi] = [[mul(x, y) for y in range(N)] for x in range(N)]
        M = tables[gi]
        c = _random_counts(k, d, rng)
        volt = [[rng.sample(range(N), c[i][j]) if c[i][j] else []
                 for j in range(k)] for i in range(k)]
        cur = _orbit_cost(N, k, volt, M)
        if cur == 0:
            return group, volt
        T0 = 2.0
        for it in range(steps):
            if time.monotonic() >= deadline:
                return None
            T = T0 * (1.0 - it / steps) + 0.05
            i = rng.randrange(k)
            j = rng.randrange(k)
            lst = volt[i][j]
            if not lst:
                continue
            t = rng.randrange(len(lst))
            g = rng.randrange(N)
            if g in lst:
                continue
            old = lst[t]
            lst[t] = g
            new = _orbit_cost(N, k, volt, M)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
                if cur == 0:
                    return group, volt
            else:
                lst[t] = old
    return None


def _orbit_phase(d, D, k, rng, deadline, state, consider):
    """Repeatedly try to beat the current best with a 2k-orbit lift of order N, N ascending."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        best_n = state['best'][0]
        N = best_n // (2 * k) + 1
        if 2 * k * N > moore:
            return
        groups = _group_list(N, rng)
        now = time.monotonic()
        slice_end = now + 0.5 * (deadline - now)
        res = _search_orbit(N, k, d, groups, rng, slice_end, 1500)
        if res is None:
            return
        group, volt = res
        darts = [(i, k + j, g) for i in range(k) for j in range(k) for g in volt[i][j]]
        try:
            n, edges = lib.group_lift(2 * k, darts, N, group[1])
            consider(n, edges)
        except Exception:
            return


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    state = {'best': best}

    def consider(n, e):
        if n > state['best'][0] and lib.is_valid(n, e, d, D):
            state['best'] = (n, e)

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return state['best']

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # New: orbit-lift annealing with k = 2 and k = 3 orbits per side.
    phase_start = time.monotonic()
    orbit_end = phase_start + 0.6 * max(0.0, deadline - phase_start)
    for k in (2, 3):
        now = time.monotonic()
        k_end = now + (orbit_end - now) * (0.5 if k == 2 else 1.0)
        try:
            _orbit_phase(d, D, k, rng, k_end, state, consider)
        except Exception:
            pass

    # Difference-cover group lifts with two base vertices (order 2N).
    hi = d * (d - 1) + 1
    lo = max(state['best'][0] // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            break
        if 2 * N <= state['best'][0]:
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

    result = state['best']
    if not lib.is_valid(result[0], result[1], d, D):
        return _fallback(d, D)
    return result
