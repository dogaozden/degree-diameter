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
    """Add or remove ordered differences of v against S[j], j != skip; return change in uncovered count."""
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


def _difference_search(d, D, floor_n, rng, deadline):
    """Difference-cover group lifts of order 2N; returns (n, edges) beating floor_n, or None."""
    best = None
    cur = floor_n
    for N in range(max(cur // 2 + 1, d), d * (d - 1) + 2):
        if time.monotonic() >= deadline:
            break
        if 2 * N <= cur:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, deadline - now)
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    tables[idx] = _ratio_table(N, groups[idx][1], groups[idx][2])
                R = tables[idx]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
        idx, S = found
        try:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, groups[idx][1])
            if n > cur and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                cur = n
        except Exception:
            pass
    return best


def _lift_edges(darts, N):
    """Edges of the Z_N lift of the 2+2 base with darts (i, j, g); A nodes i*N+x, B nodes 2N+j*N+y."""
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, 2 * N + j * N + (x + g) % N))
    return 4 * N, edges


def _voltage_anneal(d, N, rng, deadline, steps):
    """Anneal Z_N voltages on a 2+2 base (degree d, bipartite). Returns (n, edges) of diameter <= 3, or None.

    Base: A-vertices a0, a1 and B-vertices b0, b1. Darts (a0,b0) and (a1,b1) carry x voltages each,
    (a0,b1) and (a1,b0) carry d-x each, so every base vertex has degree exactly d.
    By translation symmetry, diameter <= 3 holds iff the four fibre roots reach all 4N vertices in 3 steps.
    """
    x = rng.randint(1, d - 1)
    pairs = [(0, 0, x), (1, 1, x), (0, 1, d - x), (1, 0, d - x)]
    darts = []
    for i, j, c in pairs:
        for g in rng.sample(range(N), c):
            darts.append([i, j, g])

    tot = 2 * N
    n = 4 * N

    def cost():
        A = [[], []]
        B = [[], []]
        for i, j, g in darts:
            A[i].append((j, g))
            B[j].append((i, g))
        total = 0
        for src in (0, N, tot, tot + N):
            seen = {src}
            frontier = [src]
            for _ in range(3):
                nxt = []
                for v in frontier:
                    if v < tot:
                        i, y = divmod(v, N)
                        for j, g in A[i]:
                            w = tot + j * N + (y + g) % N
                            if w not in seen:
                                seen.add(w)
                                nxt.append(w)
                    else:
                        j, y = divmod(v - tot, N)
                        for i, g in B[j]:
                            w = i * N + (y - g) % N
                            if w not in seen:
                                seen.add(w)
                                nxt.append(w)
                frontier = nxt
            total += n - len(seen)
        return total

    cur = cost()
    if cur == 0:
        return _lift_edges(darts, N)
    T0 = 1.5
    for step in range(steps):
        if step % 100 == 0 and time.monotonic() >= deadline:
            break
        T = T0 * (1.0 - step / steps) + 0.05
        k = rng.randrange(len(darts))
        i, j, old = darts[k]
        used = {g for a, b, g in darts if a == i and b == j}
        g = rng.randrange(N)
        if g in used:
            continue
        darts[k][2] = g
        new = cost()
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
            if cur == 0:
                return _lift_edges(darts, N)
        else:
            darts[k][2] = old
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
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

    # Phase 1: difference-cover lifts (the parent's construction), limited share of time.
    now = time.monotonic()
    total = max(0.0, deadline - now)
    cand = _difference_search(d, D, best[0], rng, now + 0.35 * total)
    if cand is not None:
        consider(*cand)

    # Phase 2: a different construction: Z_N lifts of a 2+2 bipartite base, giving order 4N.
    moore = lib.moore_bound(d, D)
    lo = max(best[0] // 4 + 1, 2)
    hi = moore // 4
    Ns = list(range(lo, hi + 1))
    for idx, N in enumerate(Ns):
        now = time.monotonic()
        if now >= deadline:
            break
        if 4 * N <= best[0]:
            continue
        slice_end = now + max(1.0, (deadline - now) / (len(Ns) - idx))
        slice_end = min(slice_end, deadline)
        res = None
        while res is None and time.monotonic() < slice_end:
            res = _voltage_anneal(d, N, rng, slice_end, 2500)
        if res is not None:
            try:
                consider(*res)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
