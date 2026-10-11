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


# ---- New construction: 4-block lifts (base K_{2,2} with multi-darts) ----------
# Base vertices: A0=0, A1=1 (left), B0=2, B1=3 (right). Each block has d darts,
# A0-B0 and A1-B1 carry a darts, A0-B1 and A1-B0 carry d-a darts. Group lift of
# order N gives 4N vertices, degree d, bipartite. Left multiplication is an
# automorphism, so each block is vertex-transitive and distances from one
# representative per block (4 BFS) determine the whole diameter condition.

def _cost22(N, mul, invt, darts):
    """Sum over 4 block representatives of the number of vertices at distance > 3."""
    nbr = [[] for _ in range(4)]
    for u, v, g in darts:
        nbr[u].append((v, g))
        nbr[v].append((u, invt[g]))
    total = 0
    for s in range(4):
        seen = {(s, 0)}
        frontier = [(s, 0)]
        for _ in range(3):
            nxt = []
            for b, x in frontier:
                for c, h in nbr[b]:
                    key = (c, mul(x, h))
                    if key not in seen:
                        seen.add(key)
                        nxt.append(key)
            frontier = nxt
        total += 4 * N - len(seen)
    return total


def _try_block22(d, N, rng, t_end):
    """Anneal voltages for 4-block lifts of order N. Returns (mul, darts) with zero cost, or None."""
    groups = _group_list(N, rng)
    tabs = [None] * len(groups)
    while time.monotonic() < t_end:
        gi = rng.randrange(len(groups))
        mul, inv = groups[gi][1], groups[gi][2]
        if tabs[gi] is None:
            tabs[gi] = [inv(x) for x in range(N)]
        invt = tabs[gi]
        a = rng.randint(1, d - 1)
        pat = ([(0, 2)] * a + [(0, 3)] * (d - a)
               + [(1, 2)] * (d - a) + [(1, 3)] * a)
        V = [rng.randrange(N) for _ in pat]
        darts = [(u, v, V[k]) for k, (u, v) in enumerate(pat)]
        cur = _cost22(N, mul, invt, darts)
        steps = 4000
        for it in range(steps):
            if cur == 0:
                break
            if (it & 63) == 0 and time.monotonic() >= t_end:
                break
            T = 1.5 * (1.0 - it / steps) + 0.05
            k = rng.randrange(len(V))
            old = V[k]
            V[k] = rng.randrange(N)
            u, v = pat[k]
            darts[k] = (u, v, V[k])
            new = _cost22(N, mul, invt, darts)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                V[k] = old
                darts[k] = (u, v, old)
        if cur == 0:
            return mul, list(darts)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
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

    # Difference-cover Haar lifts (order 2N): limited share of the time budget.
    cover_deadline = time.monotonic() + 0.3 * max(0.0, deadline - time.monotonic())
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= cover_deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, cover_deadline - time.monotonic())
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

    # New search: 4-block lifts of order N, giving 4N vertices with degree d.
    cap = lib.moore_bound(d, D)
    fails = 0
    N = best_n // 4 + 1
    while fails < 3 and time.monotonic() < deadline and 4 * N <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + 0.4 * (deadline - now))
        res = _try_block22(d, N, rng, slice_end)
        if res is None:
            fails += 1
            N += 1
        else:
            mul, darts = res
            try:
                n, edges = lib.group_lift(4, darts, N, mul)
                consider(n, edges)
            except Exception:
                pass
            fails = 0
            N = best_n // 4 + 1

    return best
