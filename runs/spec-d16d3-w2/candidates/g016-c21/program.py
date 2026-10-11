import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc-extension fallback (parent construction, kept as a
# safe baseline; for d = 16, D = 3 it yields the record order 394).
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, E_c = _arc_graph(m, edges, point_lines, line_points, S)
        out.append((n_c, E_c))
    return out


# ----------------------------------------------------------------------------
# New construction: cyclic Haar graphs from near-difference sets.
#
# The Haar graph H(m, S) has parts a_i, b_j with a_i ~ b_{i+s} for s in S.
# Diameter 3 holds iff
#   (1) every nonzero residue of Z_m is a difference s - t (s, t in S):
#       this gives same-side distance 2;
#   (2) S - S + S covers Z_m: this gives cross distance <= 3.
# A set S of size d with all nonzero differences covered needs
# m <= d(d-1) + 1, so the order 2m approaches the Moore bound 2(d^2-d+1).
# We search for such S by simulated annealing on the number of uncovered
# residues, then verify the result with lib.is_valid.
# ----------------------------------------------------------------------------

def _cover_search(m, k, rng, deadline):
    """Anneal a k-subset S of Z_m so that S - S covers all nonzero residues. Returns S or None."""
    S = rng.sample(range(m), k)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.35
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if inS[y]:
            continue
        old = unc
        others = [S[j] for j in range(k) if j != i]
        # remove x
        for s in others:
            r = (x - s) % m
            cnt[r] -= 1
            if cnt[r] == 0:
                unc += 1
            r = (s - x) % m
            cnt[r] -= 1
            if cnt[r] == 0:
                unc += 1
        # add y
        for s in others:
            r = (y - s) % m
            if cnt[r] == 0:
                unc -= 1
            cnt[r] += 1
            r = (s - y) % m
            if cnt[r] == 0:
                unc -= 1
            cnt[r] += 1
        delta = unc - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
        else:
            # revert: remove y, add x
            for s in others:
                r = (y - s) % m
                cnt[r] -= 1
                if cnt[r] == 0:
                    unc += 1
                r = (s - y) % m
                cnt[r] -= 1
                if cnt[r] == 0:
                    unc += 1
            for s in others:
                r = (x - s) % m
                if cnt[r] == 0:
                    unc -= 1
                cnt[r] += 1
                r = (s - x) % m
                if cnt[r] == 0:
                    unc -= 1
                cnt[r] += 1
    return S


def _haar_attempt(m, d, D, rng, deadline):
    """Try to build a valid Haar graph of order 2m with degree d. Returns (n, edges) or None."""
    S = _cover_search(m, d, rng, deadline)
    if S is None:
        return None
    n, E = lib.haar_graph(m, S)
    if lib.is_valid(n, E, d, D):
        return n, E
    return None


def _search_haar(d, D, rng, deadline):
    """Binary search over odd m for the largest feasible cyclic Haar graph. Returns (n, edges) or None."""
    top = d * d - d + 1  # Moore-type limit for diameter 3
    ms = [m for m in range(d + 1, top + 1) if m % 2 == 1]
    if not ms:
        return None
    best = None
    lo, hi = 0, len(ms) - 1
    while lo <= hi:
        now = time.monotonic()
        remain = deadline - now
        if remain < 0.5:
            break
        mid = (lo + hi) // 2
        budget = min(remain, max(3.0, remain / 3), 10.0)
        res = _haar_attempt(ms[mid], d, D, rng, now + budget)
        if res is not None:
            best = res
            lo = mid + 1
        else:
            hi = mid - 1
    return best


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D >= 3:
        # Baseline: arc-extended projective plane (record 394 for d = 16).
        arc_deadline = start + 0.2 * time_limit
        for n_c, E_c in _arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, E_c)

        # Bold change: cyclic Haar graphs from near-difference sets.
        rng = random.Random(seed * 104729 + d * 31 + D)
        res = _search_haar(d, D, rng, deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
