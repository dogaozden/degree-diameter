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


# ---------------------------------------------------------------- phase 1: difference-cover lifts

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


def _difference_phase(d, best_n, rng, p1_end, consider):
    """Parent-style search: 2N-vertex group lifts with S S^{-1} = G, N ascending."""
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= p1_end:
            break
        if 2 * N <= best_n:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, p1_end - now)
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
        try:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, edges)
        except Exception:
            pass


# ------------------------------------------------- phase 2: bipartite voltage lifts over Z_N

# Base multigraph: k vertices on side A (indices 0..k-1) and k on side B.
# Layer s (0..d-1) joins A_i to B_{(i+s) mod k} with voltage volt[s][i] in Z_N.
# Every base vertex then has exactly d darts, so the lift has degree <= d and order 2kN.
# Layer 0 has voltages fixed to 0 (WLOG by relabelling the B fibres).
# Diameter <= 3 is checked from the 2k base representatives (A_i,0), (B_j,0): the lift
# admits the Z_N shift automorphism, so this covers all pairs.

def _volt_adj(k, N, d, volt):
    n = 2 * k * N
    off = k * N
    adj = [[] for _ in range(n)]
    for s in range(d):
        vs = volt[s]
        for i in range(k):
            j = (i + s) % k
            vi = vs[i]
            ba = i * N
            bb = off + j * N
            for g in range(N):
                a = ba + g
                b = bb + (g + vi) % N
                adj[a].append(b)
                adj[b].append(a)
    return n, adj


def _cost(n, adj, reps):
    """Total number of (representative, vertex) pairs at distance > 3."""
    tot = 0
    for r in reps:
        seen = bytearray(n)
        seen[r] = 1
        fr = [r]
        cnt = 1
        for _ in range(3):
            nx = []
            for u in fr:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nx.append(w)
            cnt += len(nx)
            fr = nx
            if not fr:
                break
        tot += n - cnt
    return tot


def _volt_search(k, N, d, rng, t_end):
    """Anneal voltages until the lift has diameter <= 3; return volt or None on timeout."""
    volt = [[0] * k] + [[rng.randrange(N) for _ in range(k)] for _ in range(d - 1)]
    reps = [b * N for b in range(2 * k)]
    n, adj = _volt_adj(k, N, d, volt)
    cur = _cost(n, adj, reps)
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= t_end:
            return None
        frac = (now - t0) / span
        T = 2.0 * (1.0 - frac) + 0.05
        s = rng.randrange(1, d)
        i = rng.randrange(k)
        old = volt[s][i]
        new = rng.randrange(N)
        if new == old:
            continue
        volt[s][i] = new
        n2, adj2 = _volt_adj(k, N, d, volt)
        c = _cost(n2, adj2, reps)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            volt[s][i] = old
    return volt


def _volt_edges(k, N, d, volt):
    n, adj = _volt_adj(k, N, d, volt)
    edges = set()
    for a in range(k * N):  # side A indices are all below side B indices
        for b in adj[a]:
            edges.add((a, b))
    return n, sorted(edges)


# ----------------------------------------------------------------------- driver

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

    mb = lib.moore_bound(d, D)

    # Phase 1 (short): difference-cover group lifts, as in the parent.
    now = time.monotonic()
    p1_end = now + 0.25 * max(0.0, deadline - now)
    try:
        _difference_phase(d, best_n, rng, p1_end, consider)
    except Exception:
        pass

    # Phase 2: bipartite voltage lifts with k = 2, 3 base vertices per side.
    cands = []
    for k in (2, 3):
        for N in range(2, mb // (2 * k) + 2):
            order = 2 * k * N
            if best_n < order <= mb:
                cands.append((order, k, N))
    cands.sort()

    for idx, (order, k, N) in enumerate(cands):
        if order <= best_n:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        remaining_c = len(cands) - idx
        t_end = now + min(rem, max(1.0, 1.5 * rem / remaining_c))
        try:
            volt = _volt_search(k, N, d, rng, t_end)
        except Exception:
            volt = None
        if volt is not None:
            try:
                n, e = _volt_edges(k, N, d, volt)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
