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
# Bold construction: voltage lifts of a 2+2 base bipartite multigraph.
# Base vertices A0, A1, B0, B1. Multiplicity matrix [[k, d-k], [d-k, k]] makes
# every base vertex have degree d. Lifted vertex (u, x) with u in {0..3} is
# id u*N + x. Edge a_{i,x} ~ b_{j, x*g} for each voltage g in S_ij.
# Left translation by G is an automorphism, so diameter <= 3 is equivalent to
# every ball of radius 3 around the four vertices (u, identity) covering all 4N.
# ---------------------------------------------------------------------------

def _darts(pairs, inv):
    dA = [[], []]
    dB = [[], []]
    for i, j, gs in pairs:
        for g in gs:
            dA[i].append((j, g))
            dB[j].append((i, inv(g)))
    return dA, dB


def _ball(src, N, mul, dA, dB):
    seen = {src}
    frontier = [src]
    for _ in range(3):
        nxt = []
        for v in frontier:
            u, x = divmod(v, N)
            if u < 2:
                for j, g in dA[u]:
                    w = (2 + j) * N + mul(x, g)
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            else:
                for i, gi in dB[u - 2]:
                    w = i * N + mul(x, gi)
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
        frontier = nxt
        if not frontier:
            break
    return len(seen)


def _cost(N, mul, dA, dB):
    """Number of (source, vertex) pairs left uncovered by radius-3 balls around the 4 base reps."""
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        total += 4 * N - _ball(src, N, mul, dA, dB)
    return total


def _volt_search(N, d, rng, groups, deadline, steps):
    """Annealing over voltage sets for the 2+2 base. Returns (pairs, mul) or None."""
    _, mul, inv = rng.choice(groups)
    k = rng.randint(1, d - 1)
    specs = [(0, 0, k), (0, 1, d - k), (1, 0, d - k), (1, 1, k)]
    pairs = [[i, j, rng.sample(range(N), m)] for i, j, m in specs]
    dA, dB = _darts(pairs, inv)
    cur = _cost(N, mul, dA, dB)
    for it in range(steps):
        if cur == 0:
            break
        if (it & 63) == 0 and time.monotonic() >= deadline:
            return None
        T = 1.5 * (1 - it / steps) + 0.05
        p = pairs[rng.randrange(4)]
        gs = p[2]
        t = rng.randrange(len(gs))
        g_new = rng.randrange(N)
        if g_new in gs:
            continue
        old = gs[t]
        gs[t] = g_new
        dA, dB = _darts(pairs, inv)
        new = _cost(N, mul, dA, dB)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            gs[t] = old
    if cur != 0:
        return None
    return pairs, mul


def _lift_edges(N, pairs, mul):
    edges = []
    for i, j, gs in pairs:
        for g in gs:
            for x in range(N):
                edges.append((i * N + x, (2 + j) * N + mul(x, g)))
    return 4 * N, edges


# ---------------------------------------------------------------------------
# Parent's difference-cover Haar lift search (kept as a second phase).
# ---------------------------------------------------------------------------

def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
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

    # Phase 1 (bold): voltage lifts of a 2+2 base multigraph, order 4N.
    volt_deadline = start + 0.6 * (deadline - start)
    N = best_n // 4 + 1
    max_N = lib.moore_bound(d, 3) // 4
    while N <= max_N and N >= d and time.monotonic() < volt_deadline:
        groups = _group_list(N, rng)
        now = time.monotonic()
        n_deadline = now + 0.5 * (volt_deadline - now)
        res = None
        while res is None and time.monotonic() < n_deadline:
            res = _volt_search(N, d, rng, groups, n_deadline, 2500)
        if res is None:
            break
        pairs, mul = res
        try:
            n, edges = _lift_edges(N, pairs, mul)
            consider(n, edges)
        except Exception:
            pass
        N += 1

    # Phase 2: difference-cover Haar lifts with the remaining time.
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
