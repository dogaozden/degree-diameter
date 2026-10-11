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
# Bold branch: voltage lifts of a p+p bipartite base (p >= 2) over a group G.
# Base vertices: A-vertices 0..p-1, B-vertices p..2p-1. Each of d "darts" k is a
# perfect matching perms[k] from A to B, with a voltage volt[k][u] in G, so every
# base vertex has degree exactly d. The lift has 2pN vertices.
# By left-translation symmetry, diameter <= 3 holds iff the radius-3 balls around
# the 2p base vertices (identity fibre elements) cover everything.
# ---------------------------------------------------------------------------

def _uncovered(p, N, d, perms, volt, mt, ig):
    """Total number of (base rep, vertex) pairs at distance > 3. Zero means diameter <= 3."""
    out = [[] for _ in range(p)]
    inc = [[] for _ in range(p)]
    for k in range(d):
        pk = perms[k]
        vk = volt[k]
        for u in range(p):
            g = vk[u]
            v = pk[u]
            out[u].append((p + v, g))
            inc[v].append((u, ig[g]))
    full = 2 * p * N
    total = 0
    for bi in range(2 * p):
        start_id = bi * N  # group element x = 0 (identity)
        frontier = [start_id]
        seen = {start_id}
        for _ in range(3):
            nxt = []
            for sid in frontier:
                b, x = divmod(sid, N)
                row = mt[x]
                if b < p:
                    for nb, g in out[b]:
                        nid = nb * N + row[g]
                        if nid not in seen:
                            seen.add(nid)
                            nxt.append(nid)
                else:
                    for u, gi in inc[b - p]:
                        nid = u * N + row[gi]
                        if nid not in seen:
                            seen.add(nid)
                            nxt.append(nid)
            frontier = nxt
            if not frontier:
                break
        total += full - len(seen)
    return total


def _lift_anneal(p, N, d, mt, ig, rng, deadline):
    """Anneal perms and voltages to zero uncovered pairs. Returns (perms, volt) or None."""
    perms = [rng.sample(range(p), p) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(p)] for _ in range(d)]
    cur = _uncovered(p, N, d, perms, volt, mt, ig)
    steps = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        steps += 1
        T = max(0.15, 1.5 * 0.9995 ** steps)
        k = rng.randrange(d)
        if rng.random() < 0.1:
            old = perms[k]
            perms[k] = rng.sample(range(p), p)
            new = _uncovered(p, N, d, perms, volt, mt, ig)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                perms[k] = old
        else:
            u = rng.randrange(p)
            old = volt[k][u]
            volt[k][u] = rng.randrange(N)
            new = _uncovered(p, N, d, perms, volt, mt, ig)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                volt[k][u] = old
    return perms, volt


def _lift_phase(p, d, rng, deadline, best_n):
    """Yield (n, edges) for each lift found, for increasing group orders N."""
    moore = lib.moore_bound(d, 3)
    for N in range(max(2, best_n // (2 * p) + 1), moore // (2 * p) + 1):
        if time.monotonic() >= deadline:
            return
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.6 * max(0.0, deadline - time.monotonic())
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                now = time.monotonic()
                if now >= deadline_N:
                    break
                if tables[idx] is None:
                    _, mul, inv = groups[idx]
                    mt = [[mul(x, y) for y in range(N)] for x in range(N)]
                    ig = [inv(y) for y in range(N)]
                    tables[idx] = (mt, ig)
                mt, ig = tables[idx]
                res = _lift_anneal(p, N, d, mt, ig, rng, min(deadline_N, now + 3.0))
                if res is not None:
                    found = (idx, res[0], res[1])
                    break
        if found is None:
            return
        idx, perms, volt = found
        mul = groups[idx][1]
        darts = [(u, p + perms[k][u], volt[k][u]) for k in range(d) for u in range(p)]
        n, edges = lib.group_lift(2 * p, darts, N, mul)
        yield n, edges


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

    # Phase 1: difference-cover Haar lifts (p = 1), as in the parent.
    p1_deadline = start + 0.3 * budget
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= p1_deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, p1_deadline - time.monotonic())
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

    # Phase 2 and 3: bold voltage lifts of 2p-vertex-per-side bases, p = 2 then 3.
    for p, frac in ((2, 0.7), (3, 1.0)):
        phase_deadline = start + frac * budget
        for n, e in _lift_phase(p, d, rng, phase_deadline, best_n):
            consider(n, e)

    return best
