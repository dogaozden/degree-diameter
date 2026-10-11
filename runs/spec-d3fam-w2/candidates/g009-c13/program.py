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
# New construction: multi-orbit voltage lifts with annealed voltages.
#
# A bipartite base graph has k "A" vertices and k "B" vertices. Its darts are
# given by a d-regular k x k multiplicity matrix M (a sum of d random permutation
# matrices), and every dart (i, j) carries M[i][j] distinct voltages from a group G
# of order N. The lift has 2kN vertices A_{i,x}, B_{j,y} with A_{i,x} ~ B_{j,x*g}
# for each dart (i, j, g). Left multiplication is an automorphism that acts
# regularly on each orbit, so diameter <= 3 only needs checking from the 2k
# representatives A_{i,e} and B_{j,e}. Voltages are annealed to minimize the number
# of vertices left unreached within distance 3.
# ---------------------------------------------------------------------------

def _groups_of_order(N):
    """Multiplication functions for cyclic and semidirect groups of order N."""
    out = [lib.cyclic_group(N)[1]]
    for kk in range(2, N + 1):
        if N % kk:
            continue
        m = N // kk
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                try:
                    out.append(lib.semidirect_group(m, kk, r)[1])
                except ValueError:
                    pass
    return out


def _rand_matrix(k, d, rng):
    """k x k nonnegative integer matrix with all row and column sums equal to d."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            M[i][perm[i]] += 1
    return M


def _cost(adj, n, srcs):
    """Total number of vertices not within distance 3 of each source vertex."""
    total = 0
    for s in srcs:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(3):
            new = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        new.append(v)
            cnt += len(new)
            frontier = new
            if not frontier:
                break
        total += n - cnt
    return total


def _anneal_once(k, N, d, mul, rng, steps, end):
    """One annealing run. Returns (n, edges) with diameter <= 3 on the lift, or None."""
    n = 2 * k * N
    base_b = k * N
    mulT = [[mul(x, g) for g in range(N)] for x in range(N)]
    M = _rand_matrix(k, d, rng)
    pairs = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    V = {p: rng.sample(range(N), M[p[0]][p[1]]) for p in pairs}
    adj = [set() for _ in range(n)]

    def dart(p, g, add):
        i, j = p
        for x in range(N):
            a = i * N + x
            b = base_b + j * N + mulT[x][g]
            if add:
                adj[a].add(b)
                adj[b].add(a)
            else:
                adj[a].discard(b)
                adj[b].discard(a)

    for p in pairs:
        for g in V[p]:
            dart(p, g, True)
    srcs = [i * N for i in range(k)] + [base_b + j * N for j in range(k)]
    cur = _cost(adj, n, srcs)
    for it in range(steps):
        if cur == 0:
            break
        if time.monotonic() >= end:
            return None
        T = 0.6 * (1.0 - it / steps) + 0.03
        p = rng.choice(pairs)
        lst = V[p]
        idx = rng.randrange(len(lst))
        g_old = lst[idx]
        g_new = rng.randrange(N)
        while g_new in lst:
            g_new = rng.randrange(N)
        dart(p, g_old, False)
        dart(p, g_new, True)
        new = _cost(adj, n, srcs)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            lst[idx] = g_new
            cur = new
        else:
            dart(p, g_new, False)
            dart(p, g_old, True)
    if cur != 0:
        return None
    edges = [(i * N + x, base_b + j * N + mulT[x][g])
             for (i, j) in pairs for g in V[(i, j)] for x in range(N)]
    return n, edges


def _search_lift(k, N, d, groups, rng, end):
    """Restart annealing with random groups and matrices until success or time runs out."""
    while time.monotonic() < end:
        mul = rng.choice(groups)
        res = _anneal_once(k, N, d, mul, rng, 2500, end)
        if res is not None:
            return res
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
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

    # New: multi-orbit voltage lifts (k per side, lift order 2kN), annealed.
    bound = lib.moore_bound(d, 3)
    search_end = start + 0.75 * total
    cands = []
    for k in (2, 3):
        for N in range(2, bound // (2 * k) + 1):
            order = 2 * k * N
            if best_n < order <= bound:
                cands.append((order, k, N))
    cands.sort()
    group_cache = {}
    for idx, (order, k, N) in enumerate(cands):
        if order <= best_n:
            continue
        now = time.monotonic()
        if now >= search_end:
            break
        share = (search_end - now) / (len(cands) - idx)
        if N not in group_cache:
            group_cache[N] = _groups_of_order(N)
        res = _search_lift(k, N, d, group_cache[N], rng, now + share)
        if res is not None:
            consider(*res)

    # Difference-cover Haar lifts (order 2N with S S^{-1} = G, |S| = d).
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
            for gi in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[gi] is None:
                    mul, inv = groups[gi][1], groups[gi][2]
                    tables[gi] = _ratio_table(N, mul, inv)
                R = tables[gi]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
                if S is not None:
                    found = (gi, S)
                    break
        if found is None:
            break
        gi, S = found
        mul = groups[gi][1]
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
        consider(n, edges)

    return best
