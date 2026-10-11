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


# ---------------------------------------------------------------------------
# Phase 1 (new construction): 2-vertex-per-side group lifts.
# Vertices: A(i, x) = i*N + x (i in {0,1}), B(j, y) = 2N + j*N + y.
# Dart (i, j, s) joins A(i, x) to B(j, x*s). Block (i,j) carries c_ij distinct
# voltages, with c_00 = c_11 = c and c_01 = c_10 = d - c, so every vertex has
# degree d. Left multiplication is an automorphism, so diameter <= 3 holds iff
# the ball of radius 3 around each of the 4 class representatives covers all
# 4N vertices. The annealer minimises the total number of uncovered vertices.
# ---------------------------------------------------------------------------

def _lift_cost(N, MT, V):
    """Total number of vertices missed by the radius-3 balls around the 4 class representatives."""
    n = 4 * N
    adj = [[] for _ in range(n)]
    for i in (0, 1):
        for j in (0, 1):
            base_b = 2 * N + j * N
            for s in V[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = base_b + MT[x][s]
                    adj[a].append(b)
                    adj[b].append(a)
    total = 0
    for r in (0, N, 2 * N, 3 * N):
        seen = {r}
        frontier = [r]
        for _ in range(3):
            nxt = []
            for v in frontier:
                for u in adj[v]:
                    if u not in seen:
                        seen.add(u)
                        nxt.append(u)
            frontier = nxt
        total += n - len(seen)
    return total


def _anneal_lift(N, d, groups, rng, deadline):
    """Search for a valid 4N-vertex lift. Returns (mul, MT, V) or None."""
    mt_cache = {}
    steps = 3000
    while time.monotonic() < deadline:
        idx = rng.randrange(len(groups))
        mul = groups[idx][1]
        if idx not in mt_cache:
            mt_cache[idx] = [[mul(x, s) for s in range(N)] for x in range(N)]
        MT = mt_cache[idx]
        c = rng.randint(1, d - 1)
        sizes = [[c, d - c], [d - c, c]]
        V = [[rng.sample(range(N), sizes[i][j]) for j in range(2)] for i in range(2)]
        cost = _lift_cost(N, MT, V)
        for it in range(steps):
            if cost == 0:
                return mul, MT, V
            if time.monotonic() >= deadline:
                return None
            T = 0.2 + 1.5 * (1.0 - it / steps)
            i = rng.randrange(2)
            j = rng.randrange(2)
            idx2 = rng.randrange(len(V[i][j]))
            old = V[i][j][idx2]
            cur = set(V[i][j])
            x = rng.randrange(N)
            while x in cur:
                x = rng.randrange(N)
            V[i][j][idx2] = x
            new_cost = _lift_cost(N, MT, V)
            delta = new_cost - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = new_cost
            else:
                V[i][j][idx2] = old
        if cost == 0:
            return mul, MT, V
    return None


def _lift_edges(N, MT, V):
    edges = []
    for i in (0, 1):
        for j in (0, 1):
            for s in V[i][j]:
                for x in range(N):
                    edges.append((i * N + x, 2 * N + j * N + MT[x][s]))
    return 4 * N, edges


# ---------------------------------------------------------------------------
# Phase 2 (parent's construction): Haar lifts from difference covers.
# ---------------------------------------------------------------------------

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

    # Phase 1: 2-vertex-per-side lifts over (semidirect) groups, aiming at orders 4N > best_n.
    total = max(0.0, deadline - time.monotonic())
    phase1_end = time.monotonic() + 0.55 * total
    hi4 = (d * d - d + 1) // 2 + 1  # 4N must stay within the D=3 Moore bound 2(d^2-d+1)
    N = max(best_n // 4 + 1, 2)
    while N <= hi4 and time.monotonic() < phase1_end:
        groups = _group_list(N, rng)
        cap = time.monotonic() + 0.5 * max(0.0, phase1_end - time.monotonic())
        res = _anneal_lift(N, d, groups, rng, min(cap, phase1_end))
        if res is None:
            break
        mul, MT, V = res
        n, edges = _lift_edges(N, MT, V)
        consider(n, edges)
        N = max(N + 1, best_n // 4 + 1)

    # Phase 2: difference-cover Haar lifts, order 2N with S S^{-1} = G and |S| = d.
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

    return best
