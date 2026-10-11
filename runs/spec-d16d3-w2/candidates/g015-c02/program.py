import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 1 (main bet for D = 3): Haar graphs from difference bases.
#
# Haar graph H(m, S): A_i ~ B_{i+s} for s in S, |S| = d. It is d-regular and
# bipartite. If every nonzero residue of Z_m is a difference s - t (S - S = Z_m),
# then any two A's are at distance 2, any two B's at distance 2, and any A-B pair
# is at distance <= 3 (since y lies in S + (S - S) = Z_m). So diameter 3 holds
# and the order is 2m. The search below looks for such S of size d in Z_m with m
# as large as possible. The cover count is O(d) per move, far cheaper than
# checking the whole graph.
# ----------------------------------------------------------------------------

def _swap(S, i, y, cnt, m):
    """Replace S[i] by y, updating the ordered-difference counts cnt.

    Returns the change in the number of uncovered nonzero residues.
    Calling it again with (S, i, old_value) reverts the move and returns the negated delta.
    """
    x = S[i]
    others = S[:i] + S[i + 1:]
    delta = 0
    for s in others:
        r = (x - s) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            delta += 1
        r = (s - x) % m
        cnt[r] -= 1
        if cnt[r] == 0:
            delta += 1
    for s in others:
        r = (y - s) % m
        if cnt[r] == 0:
            delta -= 1
        cnt[r] += 1
        r = (s - y) % m
        if cnt[r] == 0:
            delta -= 1
        cnt[r] += 1
    S[i] = y
    return delta


def _diff_search(m, k, rng, deadline):
    """Find S subset of Z_m with 0 in S, |S| = k and S - S = Z_m, by simulated annealing.

    Returns sorted S or None if the deadline passes first.
    """
    if k < 1 or k > m:
        return None
    iters = 150000
    while True:
        if time.monotonic() >= deadline:
            return None
        S = [0] + rng.sample(range(1, m), k - 1)
        inS = [False] * m
        for s in S:
            inS[s] = True
        cnt = [0] * m
        for a in S:
            for b in S:
                if a != b:
                    cnt[(a - b) % m] += 1
        unc = sum(1 for r in range(1, m) if cnt[r] == 0)
        for it in range(iters):
            if unc == 0:
                return sorted(S)
            if (it & 2047) == 0 and time.monotonic() >= deadline:
                return None
            T = 0.6 * (0.03 / 0.6) ** (it / iters)
            i = rng.randrange(1, k)
            y = rng.randrange(1, m)
            if inS[y]:
                continue
            x = S[i]
            delta = _swap(S, i, y, cnt, m)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                unc += delta
                inS[x] = False
                inS[y] = True
            else:
                _swap(S, i, x, cnt, m)
        if unc == 0:
            return sorted(S)


def _haar_climb(d, m_lo, m_hi, rng, deadline):
    """Climb m upward from m_lo; return (m, S) for the largest m solved, or None."""
    found = None
    m = m_lo
    while m <= m_hi:
        now = time.monotonic()
        if now >= deadline:
            break
        cap = now + 0.5 * (deadline - now)
        S = _diff_search(m, d, rng, cap)
        if S is None:
            break
        found = (m, S)
        m += 1
    return found


# ----------------------------------------------------------------------------
# Family 2 (fallback for D = 3): arc-extended projective plane graphs.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


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
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large S with all loads <= s, starting from feasible S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng, threshold):
    """Return (n, edges) candidates for prime powers q with q + 1 <= d (arc-extended PG)."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is Moore-optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Projective plane base (exact for calibration cases such as d = 3).
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Arc-extended PG: a short slice, since it is the fallback for the target.
        for n_c, e_c in _arc_extensions(d, start + 0.3 * budget,
                                        random.Random(seed * 7919 + d), best_n):
            consider(n_c, e_c)

        # Main bet: Haar graphs from difference bases, climbing m past the current best.
        m_lo = max(d, best_n // 2 + 1)
        m_hi = d * (d - 1) + 1
        if m_lo <= m_hi:
            found = _haar_climb(d, m_lo, m_hi, rng, deadline)
            if found is not None:
                m_f, S_f = found
                n_h, e_h = lib.haar_graph(m_f, S_f)
                consider(n_h, e_h)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
