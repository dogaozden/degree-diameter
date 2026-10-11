import math
import random
import time

import lib


def _pg_conic(d):
    """PG(2,q) incidence plus one A-vertex per point of a conic S_A and one B-vertex per
    line of the same conic S_B, for q the largest prime power with q + 1 <= d.
    Degree constraints are checked explicitly. Diameter 3 holds for any such loads."""
    q = next((c for c in range(d - 1, 1, -1) if lib.is_prime_power(c)), None)
    if q is None:
        return None
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    s = d - q - 1
    if s < 2:
        return n2, edges
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        cs.append(index[(0, 1, 0)])
    if len(set(cs)) != len(cs):
        return n2, edges
    pl = [[] for _ in range(m)]   # point -> line indices
    lp = [[] for _ in range(m)]   # line -> point indices
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    cl = [0] * m
    cp = [0] * m
    for P in cs:
        for L in pl[P]:
            cl[L] += 1
    for j in cs:
        for Q in lp[j]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return n2, edges
    k = len(cs)
    E = list(edges)
    for t, P in enumerate(cs):
        x = n2 + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(cs):
        b = n2 + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n2 + 2 * k, E


def _upd(cnt, others, x, sign, m):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between x and each
    element of `others`. Returns the change in the number of uncovered residues."""
    dU = 0
    for t in others:
        for r in ((x - t) % m, (t - x) % m):
            if sign > 0:
                if cnt[r] == 0:
                    dU -= 1
                cnt[r] += 1
            else:
                cnt[r] -= 1
                if cnt[r] == 0:
                    dU += 1
    return dU


def _diff_cover(k, m, rng, deadline):
    """Search for S in Z_m, |S| = k, 0 in S, with S - S = Z_m (a difference cover).
    The Haar graph of such an S has diameter 3. Simulated annealing on the number of
    uncovered nonzero residues, with restarts."""
    if m < k or m > k * (k - 1) + 1:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), k - 1)
        cnt = [0] * m
        for a in S:
            for b in S:
                if a != b:
                    cnt[(a - b) % m] += 1
        U = sum(1 for r in range(1, m) if cnt[r] == 0)
        T = rng.choice((0.4, 0.6, 0.8))
        for it in range(200000):
            if U == 0:
                return S
            if (it & 255) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(1, k)
            x = rng.randrange(1, m)
            if x in S:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            d1 = _upd(cnt, others, old, -1, m)
            d2 = _upd(cnt, others, x, +1, m)
            delta = d1 + d2
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[i] = x
                U += delta
            else:
                _upd(cnt, others, x, -1, m)
                _upd(cnt, others, old, +1, m)
        if U == 0:
            return S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Structured base: PG(2,q) with conic extension (order 394 for d = 16).
    pc = _pg_conic(d)
    if pc is not None:
        consider(pc[0], pc[1])

    # Bold family: Haar graphs H(m, S) with S a difference cover of Z_m, |S| = d.
    # Order 2m, diameter 3, degree d. Search m upward from the current record.
    mmax = d * (d - 1) + 1
    m = max(d, best_n // 2 + 1)
    fails = 0
    while m <= mmax and fails < 3:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        S = _diff_cover(d, m, rng, now + min(remaining, 10.0))
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)
            fails = 0
        else:
            fails += 1
        m += 1

    return best
