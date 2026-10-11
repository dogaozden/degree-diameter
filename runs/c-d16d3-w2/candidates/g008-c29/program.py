import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# Main new construction: a Haar-type bi-Cayley graph over a finite group G of
# order n. Pick S with |S| = d and put A_x adjacent to B_{x s} for s in S. Then
#   * A-A distance <= 2 iff x^-1 y lies in S S^-1,
#   * B-B distance <= 2 iff z^-1 w lies in S^-1 S,
#   * A-B distance <= 3 whenever S S^-1 = G (because 1 is in S).
# So S S^-1 = G and S^-1 S = G give a d-regular bipartite graph of order 2n
# and diameter 3. The Moore-type ceiling is n <= d^2 - d + 1. Finding such S
# is a difference-cover problem, solved here by simulated annealing that
# maximises the number of covered group elements.
#
# Safety: the fallbacks are K_{d,d} (valid for D >= 2), the projective plane
# when d-1 is a prime power, and the arc-extended projective plane graphs from
# the parent. Every candidate passes lib.is_valid before it can be returned.
# ----------------------------------------------------------------------------


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (parent construction, kept as
# a safety net that is strong for d = 16).
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
    return out


# ----------------------------------------------------------------------------
# Difference-cover search over finite groups (new construction).
# ----------------------------------------------------------------------------

def _groups_of_order(n, rng):
    """A few groups of order n: the cyclic group plus some semidirect products Z_m x| Z_k."""
    gs = [lib.cyclic_group(n)]
    for k in range(2, n + 1):
        if n % k:
            continue
        m = n // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        for r in rng.sample(rs, min(2, len(rs))):
            try:
                gs.append(lib.semidirect_group(m, k, r))
            except ValueError:
                continue
    rng.shuffle(gs)
    return gs[:4]


def _bump(c, g, sign, cov, w):
    """Add or remove one count for element g; track how many elements are covered."""
    if sign > 0:
        if c[g] == 0:
            cov[w] += 1
        c[g] += 1
    else:
        c[g] -= 1
        if c[g] == 0:
            cov[w] -= 1


def _dc_apply(S, x, sign, mul, invs, cnt, cov):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs of S that involve x.

    x must be in S. c1 counts s*t^-1 (covers A-A pairs), c2 counts s^-1*t (covers B-B pairs).
    """
    c1, c2 = cnt
    ix = invs[x]
    for t in S:
        _bump(c1, mul(x, invs[t]), sign, cov, 0)
        _bump(c2, mul(ix, t), sign, cov, 1)
    for t in S:
        if t != x:
            _bump(c1, mul(t, ix), sign, cov, 0)
            _bump(c2, mul(invs[t], x), sign, cov, 1)


def _sa(n, mul, invs, d, rng, t_end):
    """Anneal a d-subset S of the group (with identity in S) so that S S^-1 and S^-1 S both cover G.

    Returns S on success, None if time runs out.
    """
    S = [0]
    c1 = [0] * n
    c2 = [0] * n
    cnt = (c1, c2)
    cov = [0, 0]
    S_cur = []
    for x in [0] + rng.sample(range(1, n), d - 1):
        S_cur.append(x)
        _dc_apply(S_cur, x, 1, mul, invs, cnt, cov)
    S = S_cur
    temp = 0.5
    it = 0
    while True:
        if cov[0] == n and cov[1] == n:
            return list(S)
        if (it & 255) == 0 and time.monotonic() > t_end:
            return None
        it += 1
        idx = rng.randrange(1, d)
        x = S[idx]
        y = rng.randrange(n)
        while y in S:
            y = rng.randrange(n)
        before = cov[0] + cov[1]
        _dc_apply(S, x, -1, mul, invs, cnt, cov)
        S[idx] = y
        _dc_apply(S, y, 1, mul, invs, cnt, cov)
        delta = cov[0] + cov[1] - before
        if delta < 0 and rng.random() >= math.exp(delta / temp):
            _dc_apply(S, y, -1, mul, invs, cnt, cov)
            S[idx] = x
            _dc_apply(S, x, 1, mul, invs, cnt, cov)
        temp = max(0.05, temp * 0.9997)


def _difference_search(d, lo, hi, deadline, rng):
    """Ascending search over group orders n in [lo, hi]; returns (n, S, mul) for the largest success."""
    found = None
    n = lo
    while n <= hi and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(0.25, 0.5 * remaining / (hi - n + 1)))
        groups = _groups_of_order(n, rng)
        S = None
        mul = None
        gi = 0
        while S is None and time.monotonic() < slice_end:
            _, mul, inv = groups[gi % len(groups)]
            gi += 1
            invs = [inv(a) for a in range(n)]
            S = _sa(n, mul, invs, d, rng, min(slice_end, time.monotonic() + 0.15))
        if S is not None:
            found = (n, S, mul)
        n += 1
    return found


def _haar_from_group(n, mul, S):
    """Bi-Cayley graph: A_x = x, B_w = n + w, and A_x ~ B_{x*s} for s in S."""
    edges = [(x, n + mul(x, s)) for x in range(n) for s in S]
    return 2 * n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Parent's arc-extended projective plane graphs (strong safety net).
        arc = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        arc.sort(key=lambda t: -t[0])
        for n_c, e_c in arc:
            consider(n_c, e_c)

        # Projective plane incidence when d-1 is a prime power (diameter 3).
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            n_p, e_p = lib.projective_plane_incidence(d - 1)
            consider(n_p, e_p)

        # New construction: Haar-type bi-Cayley graph from a difference cover.
        # Upper bound n <= d^2 - d + 1 (Moore-type bound for this family).
        hi = d * d - d + 1
        lo = max(d, (hi * 3) // 5)
        res = _difference_search(d, lo, hi, deadline, rng)
        if res is not None:
            n_g, S, mul = res
            n_h, e_h = _haar_from_group(n_g, mul, S)
            consider(n_h, e_h)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
