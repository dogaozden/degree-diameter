"""Bold variant: Haar graphs of cyclic groups as the main construction.

For D = 3, the Haar graph H(Z_m, S) with |S| = d is bipartite, d-regular, and has
2m vertices. It has diameter <= 3 exactly when S - S covers all of Z_m. Searching for
such an S (a difference covering) with m as large as possible gives order 2m, with
the Moore-type ceiling at m = d(d-1)+1, i.e. 482 for d = 16.

Fallbacks, in order: K_{d,d}, then PG(2,q) incidence, then the Haar search, then the
arc-extension ILS from the parent. Every candidate passes lib.is_valid before it is
accepted. The Haar search is not yet tested at m near 198, so treat the gain as
unverified.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------- Haar difference covering

def _run_haar(m, k, rng, deadline, stall):
    """One annealing run for S subset of Z_m, |S| = k, 0 in S, with S - S = Z_m.

    Returns the sorted set S when every nonzero residue is a difference, or None on
    deadline or stall.
    """
    inS = [False] * m
    S = [0]
    inS[0] = True
    while len(S) < k:
        r = rng.randrange(1, m)
        if not inS[r]:
            inS[r] = True
            S.append(r)

    cnt = [0] * m  # cnt[x] = number of ordered pairs (s, t), s != t, with s - t = x
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)

    def replace(i, r):
        """Replace S[i] by r, updating cnt and the uncovered count."""
        nonlocal unc
        s = S[i]
        for j in range(k):
            if j != i:
                t = S[j]
                x = (s - t) % m
                cnt[x] -= 1
                if cnt[x] == 0:
                    unc += 1
                y = (t - s) % m
                cnt[y] -= 1
                if cnt[y] == 0:
                    unc += 1
        inS[s] = False
        inS[r] = True
        S[i] = r
        for j in range(k):
            if j != i:
                t = S[j]
                x = (r - t) % m
                if cnt[x] == 0:
                    unc -= 1
                cnt[x] += 1
                y = (t - r) % m
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1

    T = 0.35
    best_unc = unc
    last = 0
    it = 0
    while unc > 0:
        it += 1
        if (it & 4095) == 0 and time.monotonic() > deadline:
            return None
        if it - last > stall:
            return None

        r = -1
        if rng.random() < 0.8:
            # Focused move: cover a random uncovered difference u via r = t + u.
            u = -1
            for _ in range(200):
                x = rng.randrange(1, m)
                if cnt[x] == 0:
                    u = x
                    break
            if u >= 0:
                cand = (S[rng.randrange(k)] + u) % m
                if not inS[cand]:
                    r = cand
        if r < 0:
            r = rng.randrange(1, m)
            while inS[r]:
                r = rng.randrange(1, m)

        i = rng.randrange(1, k)  # index 0 stays fixed at 0
        old = S[i]
        before = unc
        replace(i, r)
        delta = unc - before
        if delta > 0 and rng.random() >= math.exp(-delta / T):
            replace(i, old)  # reject: restore exactly
        if unc < best_unc:
            best_unc = unc
            last = it
    return sorted(S)


def _haar_search(m, k, rng, deadline):
    """Restarting search for a difference covering of Z_m by k elements, before deadline."""
    while time.monotonic() < deadline:
        S = _run_haar(m, k, rng, deadline, 60000)
        if S is not None:
            return S
    return None


# ------------------------------------------------ parent's arc-extension fallback

def _pg_nbr(q):
    """Return (m, edges, nbr) for PG(2, q); nbr[x] = indices incident to x (points and lines share indices)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


def _conic_init(q):
    """Conic (plus nucleus for even q) as index set, using the same ordering as lib.projective_points."""
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _ils(m, nbr, s, rng, deadline, init):
    """Iterated local search for a large S with every X having <= s members of S in nbr[X]."""
    nbs = [set(x) for x in nbr]
    inS = [False] * m
    cnt = [0] * m
    members = set()

    def add(v):
        inS[v] = True
        members.add(v)
        for X in nbr[v]:
            cnt[X] += 1

    def remove(v):
        inS[v] = False
        members.discard(v)
        for X in nbr[v]:
            cnt[X] -= 1

    for v in init:
        if not inS[v] and all(cnt[X] < s for X in nbr[v]):
            add(v)
    best = list(members)

    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        v = rng.randrange(m)
        if inS[v]:
            continue
        full = [X for X in nbr[v] if cnt[X] >= s]
        if not full:
            add(v)
        else:
            removed = []
            pending = full
            while pending:
                X = pending[rng.randrange(len(pending))]
                cands = [Y for Y in nbr[X] if inS[Y]]
                rng.shuffle(cands)
                bestY, bestc = cands[0], -1
                for Y in cands:
                    c = 0
                    for Z in pending:
                        if Z in nbs[Y]:
                            c += 1
                    if c > bestc:
                        bestY, bestc = Y, c
                remove(bestY)
                removed.append(bestY)
                pending = [Z for Z in pending if cnt[Z] >= s]
            if len(removed) <= 1 or rng.random() < 0.01:
                add(v)
            else:
                for Y in reversed(removed):
                    add(Y)
                continue
        if len(members) > len(best):
            best = list(members)
    return best


def _arc_graph(m, edges, nbr, S):
    """PG(2,q) incidence plus an A-vertex per element of S and a B-vertex per element of S."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in nbr[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in nbr[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


# ------------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D < 3:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # 1. Projective plane incidence (diameter 3) for the largest prime power q <= d-1.
    pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    if pg_qs:
        consider(*lib.projective_plane_incidence(pg_qs[0]))

    # 2. Haar graphs H(Z_m, S) with |S| = d and S - S = Z_m: diameter 3, order 2m,
    #    m <= d(d-1)+1. Climb m upward from the current best.
    k = d
    if k >= 2:
        mmax = k * (k - 1) + 1
        m = best_n // 2 + 1
        haar_end = min(start + 0.6 * time_limit, end)
        failures = 0
        while m <= mmax and time.monotonic() < haar_end:
            now = time.monotonic()
            slice_end = min(haar_end, now + max(1.0, (haar_end - now) * 0.3))
            S = _haar_search(m, k, rng, slice_end)
            if S is None:
                failures += 1
                if failures >= 2:
                    break
                continue
            consider(*lib.haar_graph(m, S))
            m += 1

    # 3. Parent's arc-extension ILS, using whatever time remains. It is the floor
    #    that protects the earlier 394-vertex result.
    qs = [q for q in range(2, d - 1) if lib.is_prime_power(q) and q <= 23]
    if qs and time.monotonic() < end:
        data = {q: _pg_nbr(q) for q in qs}
        total = sum(data[q][0] for q in qs) or 1
        span = max(0.0, end - time.monotonic())
        for q in qs:
            m_q, edges, nbr = data[q]
            s = d - q - 1
            if s < 1:
                continue
            slice_end = time.monotonic() + span * m_q / total
            init = _conic_init(q)
            S = _ils(m_q, nbr, s, rng, slice_end, init)
            if S:
                consider(*_arc_graph(m_q, edges, nbr, S))

    return best
