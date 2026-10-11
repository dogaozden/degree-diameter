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


def _greedy_cover(N, R, d, rng, e):
    """New helper: randomized greedy difference-cover seed.

    Grows S one element at a time, always adding the element that covers the most
    still-uncovered differences (with occasional random picks for diversity).
    The result is used as a warm start for annealing.
    """
    inS = [False] * N
    covered = [False] * N
    S = [e]
    inS[e] = True
    covered[e] = True
    while len(S) < d:
        if rng.random() < 0.25:
            pool = [y for y in range(N) if not inS[y]]
            x = rng.choice(pool)
        else:
            best = -1
            cands = []
            for x in range(N):
                if inS[x]:
                    continue
                new = set()
                Rx = R[x]
                for s in S:
                    for g in (Rx[s], R[s][x]):
                        if not covered[g]:
                            new.add(g)
                gain = len(new)
                if gain > best:
                    best = gain
                    cands = [x]
                elif gain == best:
                    cands.append(x)
            x = rng.choice(cands)
        inS[x] = True
        S.append(x)
        Rx = R[x]
        for s in S:
            covered[Rx[s]] = True
            covered[R[s][x]] = True
    return S


def _anneal(N, R, d, rng, steps, e, S0=None):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found.

    If S0 is given, annealing starts from it instead of a random set.
    """
    S = list(S0) if S0 is not None else rng.sample(range(N), d)
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

    # Difference-cover Haar lifts: order 2N needs S S^{-1} = G with |S| = d.
    # Search N in descending order so the first success is the largest feasible N.
    # Each N gets an equal share of the remaining time; greedy warm starts are
    # annealed, and the search stops at the first success.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    Ns = list(range(hi, lo - 1, -1))
    for pos, N in enumerate(Ns):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(Ns) - pos)
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        while found is None and time.monotonic() < slice_end:
            for idx in range(len(groups)):
                if time.monotonic() >= slice_end:
                    break
                if tables[idx] is None:
                    mul, inv = groups[idx][1], groups[idx][2]
                    tables[idx] = _ratio_table(N, mul, inv)
                R = tables[idx]
                e = R[0][0]
                S0 = _greedy_cover(N, R, d, rng, e)
                S = _anneal(N, R, d, rng, 4000, e, S0=S0)
                if S is None:
                    S = _anneal(N, R, d, rng, 3000, e)
                if S is not None:
                    found = (idx, S)
                    break
        if found is not None:
            idx, S = found
            mul = groups[idx][1]
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, edges)
            break

    return best
