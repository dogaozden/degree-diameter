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


def _uncovered(N, S):
    """Number of residues mod N that are not a difference a - b (a, b in S, including 0)."""
    cov = [False] * N
    for a in S:
        for b in S:
            cov[(a - b) % N] = True
    return N - sum(cov)


# ----------------------------------------------------- new: multiplier-orbit search

def _orbits(N, mu):
    """Cycles of x -> mu*x on Z_N (mu a unit), as lists of residues."""
    seen = [False] * N
    orbs = []
    for x in range(N):
        if seen[x]:
            continue
        orb = []
        y = x
        while not seen[y]:
            seen[y] = True
            orb.append(y)
            y = (y * mu) % N
        orbs.append(orb)
    return orbs


def _exact_fill(orbs, d, rng):
    """Random greedy choice of orbit indices whose sizes sum to exactly d, or None."""
    for _ in range(60):
        order = list(range(len(orbs)))
        rng.shuffle(order)
        chosen, rem = [], d
        for i in order:
            if len(orbs[i]) <= rem:
                chosen.append(i)
                rem -= len(orbs[i])
                if rem == 0:
                    return chosen
    return None


def _orbit_anneal(N, d, orbs, rng, steps, deadline):
    """Anneal over unions of multiplier orbits (same-size swaps) to cover Z_N by differences."""
    by_size = {}
    for i, o in enumerate(orbs):
        by_size.setdefault(len(o), []).append(i)
    cur = _exact_fill(orbs, d, rng)
    if cur is None:
        return None

    def elems(idx):
        return [x for i in idx for x in orbs[i]]

    cost = _uncovered(N, elems(cur))
    T0 = 1.5
    for it in range(steps):
        if cost == 0:
            return elems(cur)
        if it % 256 == 0 and time.monotonic() >= deadline:
            break
        T = T0 * (1 - it / steps) + 0.05
        k = rng.randrange(len(cur))
        old = cur[k]
        pool = by_size[len(orbs[old])]
        new = pool[rng.randrange(len(pool))]
        if new in cur:
            continue
        cur[k] = new
        c2 = _uncovered(N, elems(cur))
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            cur[k] = old
    if cost == 0:
        return elems(cur)
    return None


def _orbit_search(N, d, rng, deadline):
    """Try many multipliers mu on cyclic Z_N; return a difference cover S of size d or None."""
    mus = [u for u in range(2, N) if math.gcd(u, N) == 1]
    if not mus:
        return None
    rng.shuffle(mus)
    k = 0
    while time.monotonic() < deadline:
        mu = mus[k % len(mus)]
        k += 1
        orbs = _orbits(N, mu)
        S = _orbit_anneal(N, d, orbs, rng, 2000, deadline)
        if S is not None:
            return S
    return None


# ------------------------------------------- parent: element annealing over groups

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


def _group_search(N, d, rng, deadline):
    """Element annealing over several groups of order N; returns (mul, S) or None."""
    groups = _group_list(N, rng)
    tables = [None] * len(groups)
    while time.monotonic() < deadline:
        for idx in range(len(groups)):
            if time.monotonic() >= deadline:
                break
            if tables[idx] is None:
                tables[idx] = _ratio_table(N, groups[idx][1], groups[idx][2])
            R = tables[idx]
            S = _anneal(N, R, d, rng, 6000, R[0][0])
            if S is not None:
                return groups[idx][1], S
    return None


# ------------------------------------------------------------------- driver

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

    # Haar lifts over groups of order N need S S^{-1} = G with |S| = d, so N <= d(d-1)+1.
    # Scan N downward: the first N that succeeds is the largest possible.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(hi, lo - 1, -1):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (N - lo + 1)
        orbit_end = now + 0.6 * share
        group_end = now + share

        # New: cyclic multiplier-orbit covers, then the element-annealing fallback.
        S = _orbit_search(N, d, rng, orbit_end)
        if S is not None:
            consider(*lib.haar_graph(N, S))
            if 2 * N == best_n:
                break
            continue

        res = _group_search(N, d, rng, group_end)
        if res is not None:
            mul, S = res
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, edges)
            if n == best_n:
                break

    return best
