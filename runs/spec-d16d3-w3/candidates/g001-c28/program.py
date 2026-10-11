import math
import random
import time

import lib


# Version 3 (bold change): for D >= 3, first search cyclic Haar graphs
# H(m, S) = lib.haar_graph(m, S) with |S| = d. Such a graph has diameter <= 3
# when S - S covers every nonzero residue mod m and S - S + S covers Z_m.
# The search is simulated annealing on the difference cover, combined with a
# binary search over m. The old projective-plane / arc-extension construction
# is kept as a fallback, and the best valid graph is returned.


def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k, S - S covering all nonzero residues and S - S + S = Z_m.

    Returns a sorted list or None if the deadline passes or no cover is found.
    """
    if k > m:
        return None
    S = rng.sample(range(m), k)
    inS = set(S)
    cnt = [0] * m  # cnt[x] = number of ordered pairs (a, b) in S with a - b = x (mod m)
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)

    def dec(x):
        nonlocal unc
        cnt[x] -= 1
        if cnt[x] == 0:
            unc += 1

    def inc(x):
        nonlocal unc
        if cnt[x] == 0:
            unc -= 1
        cnt[x] += 1

    T = 0.4
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        old = S[i]
        new = rng.randrange(m)
        if new in inS:
            continue
        others = [S[j] for j in range(k) if j != i]
        before = unc
        for b in others:
            dec((old - b) % m)
            dec((b - old) % m)
        for b in others:
            inc((new - b) % m)
            inc((b - new) % m)
        delta = unc - before
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = new
            inS.discard(old)
            inS.add(new)
        else:
            for b in others:
                dec((new - b) % m)
                dec((b - new) % m)
            for b in others:
                inc((old - b) % m)
                inc((b - old) % m)

    # Second condition: S - S + S must cover Z_m (distance-3 pairs across parts).
    sums = set()
    for s in S:
        for t in S:
            st = (s - t) % m
            for u in S:
                sums.add((st + u) % m)
    if len(sums) == m:
        return sorted(S)
    return None


def _cyclic_haar(k, rng, deadline):
    """Binary search for the largest m such that a cover search succeeds. Returns (m, S)."""
    kmax = k * (k - 1) + 1
    lo, hi = k, kmax
    bestm, bestS = k, list(range(k))  # S = all of Z_k gives K_{k,k}, diameter 2
    while lo < hi:
        now = time.monotonic()
        if now >= deadline:
            break
        mid = (lo + hi + 1) // 2
        steps = max(1, (hi - lo).bit_length())
        budget = (deadline - now) / steps
        S = _cover_search(k, mid, rng, min(deadline, now + budget))
        if S is not None:
            lo = mid
            bestm, bestS = mid, S
        else:
            hi = mid - 1
    return bestm, bestS


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


def _parent_build(d, D, seed, time_limit):
    """Projective-plane and arc-extension construction (previous parent)."""
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if pg_qs:
            consider(*lib.projective_plane_incidence(pg_qs[0]))

        qs = [q for q in range(2, d - 1) if lib.is_prime_power(q) and q <= 23]
        data = {q: _pg_nbr(q) for q in qs}
        total = sum(data[q][0] for q in qs) or 1
        span = max(0.0, deadline - time.monotonic())
        for q in qs:
            m, edges, nbr = data[q]
            s = d - q - 1
            if s < 1:
                continue
            slice_end = time.monotonic() + span * m / total
            init = _conic_init(q)
            S = _ils(m, nbr, s, rng, slice_end, init)
            if S:
                consider(*_arc_graph(m, edges, nbr, S))

    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3 and d >= 3:
        deadline = start + 0.5 * time_limit
        m, S = _cyclic_haar(d, rng, deadline)
        if 2 * m > best[0]:
            n, e = lib.haar_graph(m, S)
            if lib.is_valid(n, e, d, D):
                best = (n, e)

    cand = _parent_build(d, D, seed, 0.25 * time_limit)
    if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    return best
