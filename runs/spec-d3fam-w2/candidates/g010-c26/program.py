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


def _tables(N, mul, inv):
    """Return (R, M, iv): R[x][y] = x*y^{-1}, M[x][y] = x*y, iv[y] = y^{-1}."""
    iv = [inv(y) for y in range(N)]
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    R = [[M[x][iv[y]] for y in range(N)] for x in range(N)]
    return R, M, iv


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


def _tabu_cover(N, R, M, iv, d, rng, end):
    """Targeted tabu search for S (|S| = d) with S S^{-1} = G, using S[0] = identity.

    New move rule: pick a random uncovered group element u, and only consider
    replacements x that directly create the difference u against some S[j]
    (x = u*S[j] or x = (S[j]^{-1} u)^{-1}). Moves are scored exactly and a tabu
    list stops the search from undoing recent changes. Restarts after stalling.
    Returns S or None.
    """
    while time.monotonic() < end:
        S = [0] + rng.sample(range(1, N), d - 1)
        cnt = [0] * N
        cnt[0] = 1
        for a in S:
            for b in S:
                if a != b:
                    cnt[R[a][b]] += 1
        unc = sum(1 for c in cnt if c == 0)
        tabu = [0] * N
        it = 0
        stall = 0
        best_unc = unc
        while unc > 0 and stall < 400 and time.monotonic() < end:
            it += 1
            stall += 1
            while True:
                u = rng.randrange(N)
                if cnt[u] == 0:
                    break
            cands = []
            for i in range(1, d):
                for j in range(d):
                    if j == i:
                        continue
                    b = S[j]
                    cands.append((i, M[u][b]))
                    cands.append((i, iv[M[iv[b]][u]]))
            rng.shuffle(cands)
            inS = set(S)
            bestm = None
            bestd = None
            for i, x in cands[:60]:
                if x in inS or tabu[x] > it:
                    continue
                old = S[i]
                d1 = _upd(cnt, R, S, i, old, -1)
                d2 = _upd(cnt, R, S, i, x, +1)
                _upd(cnt, R, S, i, x, -1)
                _upd(cnt, R, S, i, old, +1)
                delta = d1 + d2
                if bestd is None or delta < bestd:
                    bestd = delta
                    bestm = (i, x)
            if bestm is None:
                continue
            i, x = bestm
            old = S[i]
            unc += _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
            S[i] = x
            tabu[old] = it + 5 + rng.randrange(6)
            if unc < best_unc:
                best_unc = unc
                stall = 0
        if unc == 0:
            return list(S)
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

    # Difference-cover group lifts of order 2N, searched in DESCENDING N.
    # Each N gets an equal slice of the remaining time; the first success is
    # the largest feasible N, so the search stops there.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    Ns = list(range(hi, lo - 1, -1))
    for k, N in enumerate(Ns):
        if 2 * N <= best_n:
            break
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(Ns) - k)
        groups = _group_list(N, rng)
        tabs = [None] * len(groups)
        found = None
        while found is None and time.monotonic() < slice_end:
            for idx in range(len(groups)):
                if time.monotonic() >= slice_end:
                    break
                _, mul, inv = groups[idx]
                if tabs[idx] is None:
                    tabs[idx] = _tables(N, mul, inv)
                R, M, iv = tabs[idx]
                sub_end = min(slice_end, time.monotonic() + 0.6)
                S = _tabu_cover(N, R, M, iv, d, rng, sub_end)
                if S is not None:
                    found = (idx, S)
                    break
        if found is not None:
            idx, S = found
            mul = groups[idx][1]
            try:
                n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
                consider(n, edges)
            except Exception:
                pass
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
