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


def _haar_search(d, st, consider, deadline, rng):
    """Difference-cover Haar lifts (order 2N with S S^{-1} = G, |S| = d)."""
    hi = d * (d - 1) + 1
    lo = st["n"] // 2 + 1
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


def _bi_cost(k, M, D):
    """Number of (source, target) pairs at distance > 3, over representatives of the 2k orbits.

    Vertex A_{a,x} = a*M + x, B_{b,y} = k*M + b*M + y. A_{a,x} ~ B_{b,x+s} for s in D[a][b].
    The lift is Z_M-invariant, so checking one representative per orbit decides the diameter.
    """
    kM = k * M
    n = 2 * kM
    cost = 0
    srcs = [a * M for a in range(k)] + [kM + b * M for b in range(k)]
    for src in srcs:
        dist = [-1] * n
        dist[src] = 0
        frontier = [src]
        for dep in (1, 2, 3):
            nxt = []
            for v in frontier:
                if v < kM:
                    a, x = divmod(v, M)
                    Da = D[a]
                    for b in range(k):
                        base = kM + b * M
                        for s in Da[b]:
                            w = base + (x + s) % M
                            if dist[w] < 0:
                                dist[w] = dep
                                nxt.append(w)
                else:
                    b, y = divmod(v - kM, M)
                    for a in range(k):
                        base = a * M
                        for s in D[a][b]:
                            w = base + (y - s) % M
                            if dist[w] < 0:
                                dist[w] = dep
                                nxt.append(w)
            frontier = nxt
        cost += dist.count(-1)
    return cost


def _anneal_bi(k, M, c, rng, deadline):
    """Find voltage sets D[a][b] (|D[a][b]| = c[a][b], distinct in Z_M) with diameter <= 3; None on timeout."""
    D = [[rng.sample(range(M), c[a][b]) for b in range(k)] for a in range(k)]
    pairs = [(a, b) for a in range(k) for b in range(k) if c[a][b] > 0]
    cost = _bi_cost(k, M, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T = 0.6
    steps = 0
    while cost > 0:
        steps += 1
        if steps % 16 == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            T = 0.6 * (1.0 - (now - t0) / span) + 0.08
        a, b = pairs[rng.randrange(len(pairs))]
        S = D[a][b]
        p = rng.randrange(len(S))
        v = rng.randrange(M)
        if v in S:
            continue
        old = S[p]
        S[p] = v
        new = _bi_cost(k, M, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            S[p] = old
    return D


def _bicoset_search(d, st, consider, deadline, rng):
    """Bi-coset lifts: 2k base vertices, Z_M voltages, every vertex of degree d.

    Order 2kM, with kM <= d^2 - d + 1 (the bipartite Moore bound). Candidates are tried in
    ascending order so that every success raises the bar for the rest.
    """
    bound = d * d - d + 1
    cands = []
    for k in (2, 3, 4):
        for M in range(2, bound // k + 1):
            if 2 * k * M > st["n"]:
                cands.append((2 * k * M, k, M))
    cands.sort()
    idx = 0
    while idx < len(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        order, k, M = cands[idx]
        idx += 1
        if order <= st["n"]:
            continue
        slots_left = len(cands) - idx + 1
        slot_end = now + (deadline - now) / slots_left
        q, r = divmod(d, k)
        if q + (1 if r else 0) > M:
            continue
        o = rng.randrange(k)
        c = [[q + (1 if (j - ii + o) % k < r else 0) for j in range(k)] for ii in range(k)]
        D = _anneal_bi(k, M, c, rng, slot_end)
        if D is not None:
            darts = [(a, k + b, s) for a in range(k) for b in range(k) for s in D[a][b]]
            n, edges = lib.voltage_lift(2 * k, darts, M)
            consider(n, edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    st = {"n": best[0], "best": best}

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)
            st["n"] = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return st["best"]

    try:
        # Moore-extremal case: incidence graph of PG(2, d-1).
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return st["best"]

        # Araujo-Pardo & Lopez record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

        # Keep the proven difference-cover Haar search, with an early slice of time.
        _haar_search(d, st, consider, start + 0.45 * total, rng)

        # New construction: bi-coset lifts with several base orbits per side.
        _bicoset_search(d, st, consider, deadline, rng)
    except Exception:
        pass

    return st["best"]
