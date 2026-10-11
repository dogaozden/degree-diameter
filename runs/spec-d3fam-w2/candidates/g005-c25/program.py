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
# New construction: multi-orbit cyclic lifts of a 2k-vertex bipartite base.
#
# The base has k "A" vertices and k "B" vertices. A d-regular bipartite
# multigraph on this base is the sum of d random permutation matchings. Each
# base dart (a, b) carries a voltage g in Z_N, so the lift has 2kN vertices.
# Because Z_N acts regularly on each fiber, distance from (u, x) to (w, y)
# equals distance from (u, 0) to (w, y - x). So diameter <= D is checked by
# one BFS per base vertex, not one per lift vertex. Voltages are annealed to
# minimise the number of uncovered (source, target) pairs.
# ----------------------------------------------------------------------------

def _random_multiplicity(k, d, rng):
    """m[a][j] = number of darts between A_a and B_j, a d-regular bipartite multigraph."""
    m = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            m[i][p[i]] += 1
    return m


def _lift_darts(k, d, N, rng):
    """Random darts [a, b, g]: A-base a in 0..k-1, B-base b in k..2k-1, distinct voltages per pair."""
    m = _random_multiplicity(k, d, rng)
    darts = []
    for a in range(k):
        for j in range(k):
            if m[a][j]:
                for g in rng.sample(range(N), m[a][j]):
                    darts.append([a, k + j, g])
    return darts


def _build_nb(k, N, darts):
    """Neighbour lists on base vertices: nb[base] = [(other_base, signed shift), ...]."""
    nb = [[] for _ in range(2 * k)]
    for a, b, g in darts:
        nb[a].append((b, g))
        nb[b].append((a, (-g) % N))
    return nb


def _ball_size(src, nb, N, V, R):
    """Number of vertices within distance R of fiber vertex (src, 0)."""
    seen = bytearray(V)
    s = src * N
    seen[s] = 1
    frontier = [s]
    cnt = 1
    for _ in range(R):
        nxt = []
        for v in frontier:
            b, x = divmod(v, N)
            for nbase, sh in nb[b]:
                w = nbase * N + (x + sh) % N
                if not seen[w]:
                    seen[w] = 1
                    nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _lift_cost(k, N, darts, R):
    """Total number of uncovered pairs, measured from one source per base vertex."""
    nb = _build_nb(k, N, darts)
    V = 2 * k * N
    tot = 0
    for src in range(2 * k):
        tot += V - _ball_size(src, nb, N, V, R)
    return tot


def _mutate_ok(darts, t, g):
    """True if setting dart t to voltage g keeps the voltages of its base pair distinct."""
    a, b = darts[t][0], darts[t][1]
    for s, (c, e, h) in enumerate(darts):
        if s != t and c == a and e == b and h == g:
            return False
    return True


def _multi_search(d, k, N, R, rng, deadline):
    """Anneal voltages for a 2k-base lift of order 2kN with radius-R diameter; darts or None."""
    while time.monotonic() < deadline:
        darts = _lift_darts(k, d, N, rng)
        cur = _lift_cost(k, N, darts, R)
        steps = 3000
        for it in range(steps):
            if cur == 0:
                return darts
            if time.monotonic() >= deadline:
                return None
            T = 1.5 * (1 - it / steps) + 0.05
            t = rng.randrange(len(darts))
            g = rng.randrange(N)
            if g == darts[t][2] or not _mutate_ok(darts, t, g):
                continue
            old = darts[t][2]
            darts[t][2] = g
            new = _lift_cost(k, N, darts, R)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                darts[t][2] = old
        if cur == 0:
            return darts
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

    # Stage A: difference-cover Haar lifts (k = 1), capped at 40% of the window.
    start_a = time.monotonic()
    deadline_a = start_a + 0.4 * max(0.0, deadline - start_a)
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    try:
        for N in range(max(lo, d), hi + 1):
            if time.monotonic() >= deadline_a:
                break
            groups = _group_list(N, rng)
            tables = [None] * len(groups)
            found = None
            deadline_N = time.monotonic() + 0.5 * max(0.0, deadline_a - time.monotonic())
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
    except Exception:
        pass

    # Stage B: multi-orbit cyclic lifts with k = 2 and k = 3 base pairs.
    moore = lib.moore_bound(d, D)
    for k, frac in ((2, 0.6), (3, 1.0)):
        now = time.monotonic()
        k_end = now + frac * max(0.0, deadline - now)
        N = max(d, best_n // (2 * k) + 1)
        while 2 * k * N <= moore and time.monotonic() < k_end:
            now = time.monotonic()
            slice_end = min(k_end, now + max(1.0, 0.4 * (k_end - now)))
            try:
                darts = _multi_search(d, k, N, D, rng, slice_end)
            except Exception:
                darts = None
            if darts is None:
                break
            n, edges = lib.group_lift(
                2 * k, [(a, b, g) for a, b, g in darts], N, lambda x, y: (x + y) % N)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
            N += 1

    return best
