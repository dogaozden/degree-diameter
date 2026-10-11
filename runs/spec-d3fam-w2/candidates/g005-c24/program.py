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
# New construction: bipartite voltage lifts of a 2k-vertex base multigraph over
# Z_N, found by simulated annealing on the number of bad (distance > 3) pairs.
# The base is d layers; layer l is a perfect matching of the k A-vertices onto
# the k B-vertices (permutation perm_l) with a voltage per A-vertex. Every base
# vertex has degree d, so the lift has max degree <= d and is bipartite.
# ---------------------------------------------------------------------------

def _cyc(N):
    return lambda x, g: (x + g) % N


def _lift_eval(k, N, layers):
    """Lift the base described by layers over Z_N; return (n, edges, bad_pair_count)."""
    darts = []
    for perm, volts in layers:
        for i in range(k):
            darts.append((i, k + perm[i], volts[i]))
    n, edges = lib.group_lift(2 * k, darts, N, _cyc(N))
    return n, edges, lib.bad_pairs(n, edges, 3)


def _lift_anneal(k, N, d, rng, deadline):
    """Anneal voltages/permutations until the lift has diameter <= 3; None on timeout."""
    layers = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        volts = [rng.randrange(N) for _ in range(k)]
        layers.append([perm, volts])

    n, edges, cost = _lift_eval(k, N, layers)
    if cost == 0:
        return n, edges
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 1.5 * (1.0 - frac) + 0.05
        l = rng.randrange(d)
        perm, volts = layers[l]
        mv = (k == 1) or rng.random() < 0.75
        if mv:
            i = rng.randrange(k)
            old = volts[i]
            volts[i] = rng.randrange(N)
        else:
            a, b = rng.sample(range(k), 2)
            perm[a], perm[b] = perm[b], perm[a]
        n2, e2, c2 = _lift_eval(k, N, layers)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return n2, e2
        else:
            if mv:
                volts[i] = old
            else:
                perm[a], perm[b] = perm[b], perm[a]
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

    moore = lib.moore_bound(d, D)

    # Phase B (new, bold): voltage lifts over Z_N with k base vertices per side.
    # Order is 2kN; try candidate orders above the current best, smallest first.
    try:
        phase_end = start + 0.6 * (deadline - start)
        tasks = []
        for k in (2, 3, 4):
            for N in range(1, moore // (2 * k) + 1):
                order = 2 * k * N
                if best_n < order <= moore:
                    tasks.append((order, k, N))
        tasks.sort()
        for idx, (order, k, N) in enumerate(tasks):
            if 2 * k * N <= best_n:
                continue
            now = time.monotonic()
            remaining = phase_end - now
            if remaining <= 0:
                break
            slot_end = now + remaining / (len(tasks) - idx)
            res = _lift_anneal(k, N, d, rng, slot_end)
            if res is not None:
                consider(*res)
    except Exception:
        pass

    # Phase C: difference-cover Haar lifts (order 2N, S S^{-1} = G with |S| = d).
    try:
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
    except Exception:
        pass

    return best
