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


# ---------------------------------------------------------------------------
# New construction: 4-orbit group lifts.
# Base graph: A0=0, A1=1 (one side), B0=2, B1=3 (other side).
# Dart counts c[i][j] between A_i and B_j, with row/column sums equal to d.
# Vertex (X, x) is index X*N + x. Lift edges: (A_i, x) ~ (B_j, x*s), s in S[i][j].
# Left multiplication by any h is an automorphism, so distances from (X, e)
# to all vertices decide validity: cost = number of vertices missed by the
# radius-3 balls around the 4 orbit representatives.
# ---------------------------------------------------------------------------

def _mo_cost(N, mul, S):
    """Number of (source, target) pairs at distance > 3, summed over the 4 orbit representatives."""
    V = 4 * N
    adj = [[] for _ in range(V)]
    for i in range(2):
        for j in range(2):
            vb = 2 + j
            for s in S[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = vb * N + mul[x][s]
                    adj[a].append(b)
                    adj[b].append(a)
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(3):
            nf = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nf.append(w)
            cnt += len(nf)
            frontier = nf
            if not frontier:
                break
        total += V - cnt
    return total


def _mo_anneal(N, mul, counts, rng, steps, deadline):
    """Find voltage sets S[i][j] (sizes counts[i][j], distinct within each pair) with zero cost."""
    S = [[rng.sample(range(N), counts[i][j]) for j in range(2)] for i in range(2)]
    cur = _mo_cost(N, mul, S)
    T0 = 2.0
    for it in range(steps):
        if cur == 0:
            return S
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        T = T0 * (1.0 - it / steps) + 0.02
        i = rng.randrange(2)
        j = rng.randrange(2)
        if counts[i][j] == 0:
            continue
        k = rng.randrange(len(S[i][j]))
        x = rng.randrange(N)
        if x in S[i][j]:
            continue
        old = S[i][j][k]
        S[i][j][k] = x
        new = _mo_cost(N, mul, S)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            S[i][j][k] = old
    return S if cur == 0 else None


# ---------------------------------------------------------------------------
# Previous construction kept as a secondary search: Haar lifts from difference covers.
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


def _haar_search(d, best_n, deadline, rng, consider):
    """Difference-cover Haar lifts of order 2N with S S^{-1} = G, |S| = d."""
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

    # New bold search: 4-orbit lifts with split dart counts. Order 4N > best_n.
    mo_deadline = start + 0.7 * (deadline - start)
    a = d // 2
    counts = [[a, d - a], [d - a, a]]
    moore = lib.moore_bound(d, D)
    lo = best_n // 4 + 1
    hi = moore // 4
    for N in range(max(lo, 2), hi + 1):
        now = time.monotonic()
        if now >= mo_deadline:
            break
        n_deadline = now + 0.5 * (mo_deadline - now)
        groups = _group_list(N, rng)
        found = None
        while found is None and time.monotonic() < n_deadline:
            g = groups[rng.randrange(len(groups))]
            mul_fn = g[1]
            mul = [[mul_fn(x, y) for y in range(N)] for x in range(N)]
            S = _mo_anneal(N, mul, counts, rng, 2500, n_deadline)
            if S is not None:
                found = (mul_fn, S)
        if found is None:
            break
        mul_fn, S = found
        darts = [(i, 2 + j, s) for i in range(2) for j in range(2) for s in S[i][j]]
        try:
            n, edges = lib.group_lift(4, darts, N, mul_fn)
            consider(n, edges)
        except Exception:
            pass

    # Secondary: previous difference-cover Haar search with the remaining time.
    _haar_search(d, best_n, deadline, rng, consider)

    return best
