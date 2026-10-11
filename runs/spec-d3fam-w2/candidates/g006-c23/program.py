import math
import random
import time

import lib


# Search parameters. Each anneal attempt is short so that many (N, group) pairs
# get tried within the time limit, rather than sinking the budget into one N.
_STEPS = 3000


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


def _greedy_start(N, R, d, rng):
    """NEW: greedy difference-cover start.

    Right-translating S by any g keeps S S^{-1} unchanged, so WLOG the identity
    (index 0 here, see semidirect_group / cyclic_group) lies in S. Then repeatedly add
    the element that covers the most still-uncovered differences with the current S.
    Ties are broken at random. The result is a far better seed than a uniform sample,
    and the annealer then only has to repair the remaining holes.
    """
    e = R[0][0]
    S = [0]
    covered = [False] * N
    covered[e] = True
    while len(S) < d:
        best_gain = -1
        cands = []
        for x in range(N):
            if x in S:
                continue
            gain = 0
            seen = set()
            for s in S:
                for g in (R[x][s], R[s][x]):
                    if not covered[g] and g not in seen:
                        seen.add(g)
                        gain += 1
            if gain > best_gain:
                best_gain = gain
                cands = [x]
            elif gain == best_gain:
                cands.append(x)
        x = rng.choice(cands)
        S.append(x)
        for s in S:
            covered[R[x][s]] = True
            covered[R[s][x]] = True
    return S


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


def _anneal(N, R, d, rng, steps, e, S0=None):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found.

    The starting set is S0 when given (e.g. from _greedy_start), else a random sample.
    Temperature decays geometrically from 1.0 to 0.05.
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
        T = 1.0 * (0.05 ** (it / steps))
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

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2 (gives 190/274/374 for d=11/13/15 targets).
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Difference-cover group lifts: order 2N needs S S^{-1} = G with |S| = d.
    # NEW: instead of stopping at the first N that fails, round-robin over all N that
    # could still beat best_n. Each attempt picks a random group of that order and
    # starts either from a greedy difference cover or a random sample. A failure at N
    # no longer ends the search, since a larger N may still succeed.
    hi = d * (d - 1) + 1
    cache = {}

    def groups_for(N):
        if N not in cache:
            cache[N] = (_group_list(N, rng), {})
        return cache[N]

    while time.monotonic() < deadline:
        lo = max(d, best_n // 2 + 1)
        ran = False
        for N in range(lo, hi + 1):
            if time.monotonic() >= deadline:
                break
            if 2 * N <= best_n:
                continue
            ran = True
            gl, tabs = groups_for(N)
            idx = rng.randrange(len(gl))
            if idx not in tabs:
                mul, inv = gl[idx][1], gl[idx][2]
                tabs[idx] = _ratio_table(N, mul, inv)
            R = tabs[idx]
            S0 = _greedy_start(N, R, d, rng) if rng.random() < 0.5 else None
            S = _anneal(N, R, d, rng, _STEPS, R[0][0], S0)
            if S is not None:
                try:
                    n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, gl[idx][1])
                    consider(n, edges)
                except Exception:
                    pass
        if not ran:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
