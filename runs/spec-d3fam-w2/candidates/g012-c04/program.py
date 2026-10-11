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
# New routine: two-fiber cyclic voltage lift for diameter 3.
#
# Base graph: A0, A1 (left) and B0, B1 (right), with darts
#   A0-B0: t,  A0-B1: d-t,  A1-B0: d-t,  A1-B1: t   (1 <= t <= d-1).
# Each dart (i, j, g) with a voltage g in Z_N lifts to a perfect matching
# (A_i, x) -- (B_j, x+g). Every vertex then has degree d, the graph is bipartite
# with 4N vertices. Translation by Z_N is an automorphism, so the diameter is at
# most 3 iff the four BFS trees from (A0,0), (A1,0), (B0,0), (B1,0) reach every
# vertex within 3 steps. Voltages are searched by simulated annealing on the
# count of unreached (source, target) pairs.
# ---------------------------------------------------------------------------

def _two_fiber_adj(N, V):
    adj = [[] for _ in range(4 * N)]
    for (i, j), gs in V.items():
        base_a = i * N
        base_b = 2 * N + j * N
        for g in gs:
            for x in range(N):
                a = base_a + x
                b = base_b + (x + g) % N
                adj[a].append(b)
                adj[b].append(a)
    return adj


def _two_fiber_cost(N, adj):
    M = 4 * N
    total = 0
    for s in (0, N, 2 * N, 3 * N):
        seen = bytearray(M)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(3):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += M - cnt
    return total


def _two_fiber_edges(N, V):
    edges = []
    for (i, j), gs in V.items():
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, 2 * N + j * N + (x + g) % N))
    return 4 * N, edges


def _anneal_two_fiber(N, d, rng, steps, deadline):
    """Return voltage dict V with zero uncovered pairs, or None."""
    t = rng.randrange(1, d)
    c = {(0, 0): t, (0, 1): d - t, (1, 0): d - t, (1, 1): t}
    V = {k: rng.sample(range(N), c[k]) for k in c}
    keys = list(c)
    cur = _two_fiber_cost(N, _two_fiber_adj(N, V))
    if cur == 0:
        return V
    for it in range(steps):
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        T = 1.0 * (1.0 - it / steps) + 0.05
        k = keys[rng.randrange(4)]
        idx = rng.randrange(len(V[k]))
        new = rng.randrange(N)
        if new in V[k]:
            continue
        old = V[k][idx]
        V[k][idx] = new
        c2 = _two_fiber_cost(N, _two_fiber_adj(N, V))
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            if cur == 0:
                return V
        else:
            V[k][idx] = old
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

    total = deadline - start
    phase_a_deadline = start + 0.3 * total

    # Phase A: difference-cover Haar lifts (order 2N, S S^{-1} = G, |S| = d).
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= phase_a_deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, phase_a_deadline - now)
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

    # Phase B: two-fiber lifts of order 4N, which must beat best_n (4N > best_n).
    moore = lib.moore_bound(d, D)
    lo_b = max(best_n // 4 + 1, d)
    hi_b = moore // 4
    for N in range(lo_b, hi_b + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        deadline_N = now + 0.5 * (deadline - now)
        V = None
        while V is None and time.monotonic() < deadline_N:
            V = _anneal_two_fiber(N, d, rng, 20000, deadline_N)
        if V is None:
            break
        n, edges = _two_fiber_edges(N, V)
        consider(n, edges)

    return best
