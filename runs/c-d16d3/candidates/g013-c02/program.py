import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# NEW MAIN IDEA: cyclic Haar graphs from difference bases.
#
# H(Z_m, S) has vertices a_i, b_i (i in Z_m), with a_i ~ b_{i+s} for s in S.
# It is bipartite and |S|-regular. If S - S covers all of Z_m, then every two
# a-vertices are at distance <= 2, every two b-vertices likewise, and every
# a-b pair is at distance <= 3 (because S - S + S then covers Z_m too). So
# diameter 3 holds. With |S| = d and m as large as possible, the order is
# 2m, and m <= d(d-1)+1 by counting differences. We search for S by simulated
# annealing on the number of uncovered differences, descending from the bound.
#
# Safe fallbacks: K_{d,d} (diameter 2) and the arc-extended projective plane
# graphs (diameter 3), which are the previous record construction.
# ----------------------------------------------------------------------------

def _diff_cost(S, m):
    """Number of nonzero residues of Z_m not expressible as a difference of two elements of S."""
    cnt = bytearray(m)
    for s in S:
        for t in S:
            if s != t:
                cnt[(s - t) % m] = 1
    return (m - 1) - sum(cnt[1:])


def _find_difference_basis(m, k, rng, t_end):
    """Search for k distinct residues S in Z_m with S - S = Z_m, until t_end. Returns S or None."""
    if k < 2 or k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    c = _diff_cost(S, m)
    if c == 0:
        return sorted(S)
    T = 1.0
    while time.monotonic() < t_end:
        i = rng.randrange(1, k)
        r = rng.randrange(1, m)
        if r in S:
            continue
        old = S[i]
        S[i] = r
        c2 = _diff_cost(S, m)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
            if c == 0:
                return sorted(S)
        else:
            S[i] = old
        T = max(0.05, T * 0.998)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3), kept as a fallback.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) arc-extended PG(2,q) candidates for prime powers q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points = _pg_data(q)
        S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Stage 1: arc-extended projective plane graphs (previous record family).
    if D >= 3:
        try:
            arcs = _arc_candidates(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:3]:
                consider(n_c, e_c)
        except Exception:
            pass

    # Stage 2 (new construction): cyclic Haar graphs with a difference basis.
    # Descend from the bound d(d-1)+1 and keep the first m that beats the current best.
    if D >= 3 and d >= 2:
        try:
            lo = best[0] // 2 + 1
            hi = d * (d - 1) + 1
            ms = list(range(hi, lo - 1, -1))
            for idx, m in enumerate(ms):
                now = time.monotonic()
                remaining = deadline - now
                if remaining <= 0:
                    break
                t_end = now + remaining / (len(ms) - idx)
                S = _find_difference_basis(m, d, rng, t_end)
                if S is not None:
                    n_h, e_h = lib.haar_graph(m, S)
                    consider(n_h, e_h)
                    break
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
