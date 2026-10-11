import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc-extended graphs (D = 3). Carried over from the parent.
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# New construction: Haar graphs over finite groups (bold change).
#
# For a group G of order M and a k-subset S of G, the Haar graph has parts
# A = {a_x} and B = {b_y}, with a_x ~ b_{x s} for s in S. It is k-regular and
# bipartite. Left multiplication is an automorphism, so the diameter is <= 3
# exactly when S S^{-1} = G (a_x to a_y is distance 2, and a-to-b is at most 3).
# With k = d we get n = 2M and M <= 1 + d(d-1), which is the Moore bound 2(1+d(d-1)).
# The search finds a difference cover of G of size k by simulated annealing,
# over cyclic groups and Z_m x| Z_k groups.
# ----------------------------------------------------------------------------

def _groups(M, rng):
    """(mul, inv) pairs for the cyclic group and a few semidirect products of order M."""
    out = []
    _, mul, inv = lib.cyclic_group(M)
    out.append((mul, inv))
    for m in range(2, M):
        if M % m:
            continue
        k2 = M // m
        if k2 < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            _, mul, inv = lib.semidirect_group(m, k2, r)
            out.append((mul, inv))
    return out


def _tables(M, mul, inv):
    tab = [[mul(x, y) for y in range(M)] for x in range(M)]
    invs = [inv(x) for x in range(M)]
    return tab, invs


def _cover_cost(S, tab, invs, M):
    """Number of group elements not of the form s t^{-1} with s, t in S (s != t), identity excluded from cost."""
    cov = [False] * M
    cov[0] = True
    for s in S:
        row = tab[s]
        for t in S:
            if t != s:
                cov[row[invs[t]]] = True
    return M - sum(cov)


def _cover_search(M, k, tab, invs, rng, deadline):
    """Anneal a k-subset of the group whose quotients cover the whole group. Returns S or None."""
    if k > M:
        return None
    S = rng.sample(range(M), k)
    c = _cover_cost(S, tab, invs, M)
    T = 0.5
    steps = 0
    since = 0
    bestc = c
    while c > 0:
        steps += 1
        if (steps & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = rng.randrange(M)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cover_cost(S, tab, invs, M)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
        if c < bestc:
            bestc = c
            since = 0
        else:
            since += 1
        if since > 30000:
            S = rng.sample(range(M), k)
            c = _cover_cost(S, tab, invs, M)
            bestc = c
            since = 0
    return S


def _haar_graph_from(M, S, tab):
    E = []
    for x in range(M):
        row = tab[x]
        for s in S:
            E.append((x, M + row[s]))
    return 2 * M, E


def _haar_search(k, rng, deadline):
    """Search increasing group orders M for a difference cover of size k. Returns (n, E) or None."""
    upper = 1 + k * (k - 1)
    M = max(k, (k * k) // 2)
    best = None
    fails = 0
    while M <= upper and time.monotonic() < deadline - 0.2:
        now = time.monotonic()
        budget = max(0.5, (deadline - now) * 0.3)
        attempt_end = min(deadline, now + budget)
        groups = _groups(M, rng)
        per = max(0.3, (attempt_end - now) / len(groups))
        found = None
        for mul, inv in groups:
            if time.monotonic() >= attempt_end:
                break
            tab, invs = _tables(M, mul, inv)
            end = min(attempt_end, time.monotonic() + per)
            S = _cover_search(M, k, tab, invs, rng, end)
            if S is not None:
                found = (M, S, tab)
                break
        if found is not None:
            best = found
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
        M += 1
    if best is None:
        return None
    M, S, tab = best
    return _haar_graph_from(M, S, tab)


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.75 * time_limit, time_limit - 6.0))
    rng = random.Random(seed * 1000003 + d * 31 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D >= 3:
        # Arc-extended projective plane graphs (parent construction).
        for n_c, E_c, _side in _arc_candidates(d, deadline, random.Random(seed * 7919 + d)):
            consider(n_c, E_c)
        # New construction: Haar graph over a group with a difference cover of size d.
        if time.monotonic() < deadline:
            res = _haar_search(d, rng, deadline)
            if res is not None:
                consider(res[0], list(res[1]))

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
