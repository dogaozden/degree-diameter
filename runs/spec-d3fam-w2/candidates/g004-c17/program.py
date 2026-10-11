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
# New routine: multiplier-invariant difference covers on Z_N.
#
# A Haar graph H(N, S) (a_i ~ b_j iff j - i in S) has diameter 3 whenever
# S - S = Z_N and |S| = d. If S is a union of orbits of x -> u*x for a unit u
# of order k, then S - S is also u-invariant, so the search space shrinks to
# unions of orbits. Here d = m*k + z with z in {0, 1} (z = 1 adds the orbit {0}).
# ---------------------------------------------------------------------------

def _unit_orders(N):
    """Return dict k -> list of units u mod N whose multiplicative order is exactly k."""
    out = {}
    for u in range(2, N):
        if math.gcd(u, N) != 1:
            continue
        x, k = u, 1
        while x != 1:
            x = x * u % N
            k += 1
        out.setdefault(k, []).append(u)
    return out


def _orbits(N, u, k):
    """Full-size (size k) orbits of x -> u*x on the nonzero elements of Z_N, as a partition."""
    seen = [False] * N
    seen[0] = True
    orbs = []
    for x in range(1, N):
        if seen[x]:
            continue
        orb = []
        y = x
        for _ in range(k):
            orb.append(y)
            seen[y] = True
            y = y * u % N
        if len(set(orb)) == k:
            orbs.append(orb)
    return orbs


def _uncovered(N, S):
    """Number of nonzero elements of Z_N that are not differences of two distinct elements of S."""
    diffs = set()
    for a in S:
        for b in S:
            if a != b:
                diffs.add((a - b) % N)
    return (N - 1) - len(diffs)


def _sa_orbits(N, pool, m, z, rng, steps):
    """Choose m disjoint orbits (plus {0} if z) whose difference set covers Z_N; None if not found."""
    if len(pool) < m or m < 1:
        return None

    def build_S(ix):
        S = [0] if z else []
        for i in ix:
            S.extend(pool[i])
        return S

    idx = rng.sample(range(len(pool)), m)
    S = build_S(idx)
    cost = _uncovered(N, S)
    if cost == 0:
        return S
    for it in range(steps):
        T = 1.0 - 0.9 * it / steps
        p = rng.randrange(m)
        q = rng.randrange(len(pool))
        if q in idx:
            continue
        new = idx[:]
        new[p] = q
        S2 = build_S(new)
        c2 = _uncovered(N, S2)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            idx, cost = new, c2
            if cost == 0:
                return build_S(idx)
    return None


def _multiplier_phase(d, lo, hi, rng, t_end):
    """Search N in [lo, hi] for multiplier-invariant covers; return (largest N, S) found or None."""
    best = None
    Ns = list(range(max(lo, d), hi + 1))
    for pos, N in enumerate(Ns):
        now = time.monotonic()
        if now >= t_end:
            break
        t_N = now + (t_end - now) / (len(Ns) - pos)
        uo = _unit_orders(N)
        configs = []
        for z in (0, 1):
            dd = d - z
            for k in uo:
                if k < 2 or dd % k or k > N - 1:
                    continue
                m = dd // k
                if m >= 1 and (N - 1) // k >= m:
                    configs.append((k, m, z))
        if not configs:
            continue
        while time.monotonic() < t_N:
            k, m, z = rng.choice(configs)
            u = rng.choice(uo[k])
            pool = _orbits(N, u, k)
            S = _sa_orbits(N, pool, m, z, rng, 3000)
            if S is not None and len(S) == d:
                best = (N, S)
                break
    return best


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

    # Phase 1: multiplier-invariant Haar lifts over cyclic groups (new routine).
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    phase1_end = start + 0.6 * (deadline - start)
    res = _multiplier_phase(d, lo, hi, rng, phase1_end)
    if res is not None:
        N, S = res
        consider(*lib.haar_graph(N, S))
        lo = best_n // 2 + 1

    # Phase 2: general difference-cover search over cyclic and semidirect groups.
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
