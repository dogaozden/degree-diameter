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


# ----------------------------------------------------------------------------
# New idea: two-orbit voltage lifts with diameter-3 cost via BFS from base reps.
#
# Base graph: k A-vertices and k B-vertices, with a k x k matrix of dart
# multiplicities M (every row and column sums to d, so the lift is d-regular).
# Each dart (a, j, g) joins (A_a, x) to (B_j, x*g) for all x in G, so the lift
# has 2*k*|G| vertices and is bipartite by construction.
#
# The lift is invariant under left multiplication by G, so the distance from
# (u, x) to (v, y) equals the distance from (u, e) to (v, x^{-1} y). Hence a
# BFS of depth 3 from the identity fibre of each base vertex (2k BFS runs in
# total) counts every bad pair. Annealing over the dart voltages minimises this
# count, which is much cheaper than a full all-pairs check.
# ----------------------------------------------------------------------------

def _bad_pairs_lift(N, k, mt, il, darts):
    """Count (source, vertex) pairs not reached within distance 3 from the 2k identity sources.

    darts: list of [a, j, g] with a in 0..k-1 (A-vertex) and j in 0..k-1 (B-vertex k+j).
    mt: multiplication table of G; il: inverse list of G.
    """
    outA = [[] for _ in range(k)]
    inB = [[] for _ in range(k)]
    for a, j, g in darts:
        outA[a].append((k + j, g))
        inB[j].append((a, il[g]))
    total = 2 * k * N
    bad = 0
    for s in range(2 * k):
        start = s * N  # identity element has index 0 in both group encodings
        seen = {start}
        frontier = [start]
        for _ in range(3):
            nxt = []
            for key in frontier:
                v, x = divmod(key, N)
                row = mt[x]
                if v < k:
                    for b, g in outA[v]:
                        nk = b * N + row[g]
                        if nk not in seen:
                            seen.add(nk)
                            nxt.append(nk)
                else:
                    for a, h in inB[v - k]:
                        nk = a * N + row[h]
                        if nk not in seen:
                            seen.add(nk)
                            nxt.append(nk)
            frontier = nxt
            if not frontier:
                break
        bad += total - len(seen)
    return bad


def _anneal_lift(N, k, M, mt, il, rng, steps, deadline):
    """Anneal distinct dart voltages for the base multiplicity matrix M; return darts or None."""
    darts = []
    pair_of = []
    used = {}
    for a in range(k):
        for j in range(k):
            c = M[a][j]
            if c == 0:
                continue
            s = rng.sample(range(N), c)
            used[(a, j)] = set(s)
            for g in s:
                darts.append([a, j, g])
                pair_of.append((a, j))
    if not darts:
        return None
    cost = _bad_pairs_lift(N, k, mt, il, darts)
    m = len(darts)
    for it in range(steps):
        if cost == 0:
            break
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break
        t = rng.randrange(m)
        p = pair_of[t]
        g_new = rng.randrange(N)
        if g_new in used[p]:
            continue
        old = darts[t][2]
        darts[t][2] = g_new
        new = _bad_pairs_lift(N, k, mt, il, darts)
        T = 2.0 * (1.0 - it / steps) + 0.05
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            used[p].discard(old)
            used[p].add(g_new)
            cost = new
        else:
            darts[t][2] = old
    if cost == 0:
        return darts
    return None


def _two_orbit_phase(d, get_best_n, rng, deadline, consider):
    """Search two-orbit (k = 2) voltage lifts of diameter 3 with order 4N above the current best."""
    k = 2
    mb = lib.moore_bound(d, 3)
    hi = mb // (2 * k)
    for N in range(max(d, get_best_n() // (2 * k) + 1), hi + 1):
        now = time.monotonic()
        if now >= deadline:
            return
        if 2 * k * N <= get_best_n():
            continue
        budget_end = now + (deadline - now) / (hi - N + 1)
        groups = _group_list(N, rng)
        tabs = []
        for order, mul, inv in groups:
            mt = [[mul(x, y) for y in range(N)] for x in range(N)]
            il = [inv(x) for x in range(N)]
            tabs.append((mt, il, mul))
        done = False
        gi = 0
        while not done and time.monotonic() < budget_end:
            mt, il, mul = tabs[gi % len(tabs)]
            gi += 1
            a = rng.randint(1, d - 1)
            M = [[a, d - a], [d - a, a]]
            darts = _anneal_lift(N, k, M, mt, il, rng, 3000, budget_end)
            if darts is not None:
                gdarts = [(x, k + y, g) for x, y, g in darts]
                n, edges = lib.group_lift(2 * k, gdarts, N, mul)
                if consider(n, edges):
                    done = True


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
            return True
        return False

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

    # Phase 1: two-orbit voltage lifts (new construction), first share of the time.
    now = time.monotonic()
    mid = now + 0.6 * max(0.0, deadline - now)
    _two_orbit_phase(d, lambda: best_n, rng, mid, consider)

    # Phase 2: difference-cover Haar lifts, using the remaining time.
    # Order 2N needs S S^{-1} = G with |S| = d.
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= deadline:
            break
        if 2 * N <= best_n:
            continue
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
