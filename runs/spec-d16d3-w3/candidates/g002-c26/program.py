import math
import random
import time

import lib


# Bold change in this version: the main route is no longer the arc extension of
# PG(2, q). Instead it is a Haar graph H(m, S) over Z_m, where S is a difference
# cover (every nonzero residue is a difference of two elements of S, with 0 in S).
# Such a graph is bipartite, has degree |S| = d, and has diameter <= 3. Its order
# is 2m, so a cover of size d = 16 with m >= 198 beats the 394 record. A simulated
# annealing search looks for the covers. The PG(2, q) incidence graph and K_{d,d}
# stay as safe fallbacks. The arc-extension ILS from the parent is kept as a
# third route for whatever time remains.


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
    """PG(2,q) incidence plus an A-vertex per element of S (joined to its lines) and a B-vertex (joined to its points)."""
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


def _find_cover(m, k, rng, deadline):
    """Find S in Z_m with 0 in S, |S| = k, and S - S covering all of Z_m (simulated annealing).

    Returns the sorted list S, or None if the deadline passes first.
    """
    if k < 2 or m < k or m > k * (k - 1) + 1:
        return None
    span = 200000  # iterations per restart
    while time.monotonic() < deadline:
        elems = [0] + rng.sample(range(1, m), k - 1)
        inS = [False] * m
        for x in elems:
            inS[x] = True
        cnt = [0] * m
        for i in range(k):
            for j in range(k):
                if i != j:
                    cnt[(elems[i] - elems[j]) % m] += 1
        unc = sum(1 for r in range(1, m) if cnt[r] == 0)
        for it in range(span):
            if unc == 0:
                return sorted(elems)
            if (it & 1023) == 0 and time.monotonic() > deadline:
                return None
            y = rng.randrange(1, m)
            if inS[y]:
                continue
            i = rng.randrange(1, k)
            x = elems[i]
            T = 0.6 * (1.0 - it / span) + 0.05
            old = unc
            # Remove x: decrement differences involving x and the other members.
            for j in range(k):
                if j != i:
                    z = elems[j]
                    for r in ((x - z) % m, (z - x) % m):
                        cnt[r] -= 1
                        if cnt[r] == 0:
                            unc += 1
            # Add y.
            for j in range(k):
                if j != i:
                    z = elems[j]
                    for r in ((y - z) % m, (z - y) % m):
                        if cnt[r] == 0:
                            unc -= 1
                        cnt[r] += 1
            delta = unc - old
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                inS[x] = False
                inS[y] = True
                elems[i] = y
            else:
                # Revert: remove y, restore x (elems is unchanged).
                for j in range(k):
                    if j != i:
                        z = elems[j]
                        for r in ((y - z) % m, (z - y) % m):
                            cnt[r] -= 1
                            if cnt[r] == 0:
                                unc += 1
                for j in range(k):
                    if j != i:
                        z = elems[j]
                        for r in ((x - z) % m, (z - x) % m):
                            if cnt[r] == 0:
                                unc -= 1
                            cnt[r] += 1
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    span = deadline - start
    haar_deadline = start + 0.55 * span
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Plain projective plane for the largest prime power q with q + 1 <= d.
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if pg_qs:
            consider(*lib.projective_plane_incidence(pg_qs[0]))

        # Route 1: Haar graphs from difference covers. Order 2m, degree d, diameter 3.
        # Only m values above the current best order are useful, so start there.
        m = max(best_n // 2 + 1, d)
        m_hi = d * (d - 1) + 1
        while m <= m_hi:
            now = time.monotonic()
            if now >= haar_deadline:
                break
            slice_end = now + max(1.0, 0.5 * (haar_deadline - now))
            S = _find_cover(m, d, rng, slice_end)
            if S is None:
                break
            consider(*lib.haar_graph(m, S))
            m += 1

        # Route 2: arc-extended PG(2, q) graphs with ILS, using the leftover time.
        qs = [q for q in range(2, d - 1) if lib.is_prime_power(q) and q <= 23]
        if qs and time.monotonic() < deadline:
            data = {q: _pg_nbr(q) for q in qs}
            total = sum(data[q][0] for q in qs) or 1
            for q in qs:
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    break
                m_q, edges, nbr = data[q]
                s = d - q - 1
                if s < 1:
                    continue
                slice_end = time.monotonic() + remaining * m_q / total
                total -= m_q
                init = _conic_init(q)
                S = _ils(m_q, nbr, s, rng, slice_end, init)
                if S:
                    consider(*_arc_graph(m_q, edges, nbr, S))

    return best
