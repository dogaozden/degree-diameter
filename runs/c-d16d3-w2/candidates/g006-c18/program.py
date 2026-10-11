import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with degree d it has spare s = d - q - 1. Choose a point set S such that
# each line holds <= s points of S and each point lies on <= s lines indexed by
# S. For each P in S add an A-vertex joined to the lines through P; for each j
# in S add a B-vertex joined to the points on line j. For d = 16, q = 13 a conic
# (14 points) gives order 2*183 + 2*14 = 394.
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
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cyclic Haar graphs from difference covers (diameter 3).
#
# For a k-subset S of Z_m, H(m, S) joins a_i to b_{i+s} for s in S. If every
# nonzero residue of Z_m is a difference s - t, then A-A distances are <= 2, and
# S - S + S = Z_m gives A-B distances <= 3. Order 2m with m <= k(k-1)+1.
#
# NEW SEARCH: guided moves. Pick a residue x that no difference yet covers,
# choose i, j, and set S[i] := S[j] + x, which creates the difference x directly.
# This replaces the blind random moves of the previous search. Restarts are used
# when a run stalls.
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    """Return (cnt, zeros): cnt[x] = #ordered pairs (s,t), s != t, with s - t = x mod m; zeros = #{x != 0 : cnt[x] = 0}."""
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    """Replace S[i] by y (y not in S), updating cnt and the zero count. Returns the new zero count."""
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            a = (old - t) % m
            b = (t - old) % m
            cnt[a] -= 1
            if cnt[a] == 0:
                zeros += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            a = (y - t) % m
            b = (t - y) % m
            if cnt[a] == 0:
                zeros -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                zeros -= 1
            cnt[b] += 1
    return zeros


def _cover_guided(k, m, deadline, rng):
    """Find a k-subset S of Z_m whose nonzero differences cover Z_m \\ {0}; return sorted S or None."""
    if k > m or k * (k - 1) + 1 < m:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        cnt, zeros = _diff_counts(S, m)
        T = 0.5
        for it in range(1, 40001):
            if zeros == 0:
                return sorted(S)
            if it % 256 == 0 and time.monotonic() > deadline:
                return None
            missing = [x for x in range(1, m) if cnt[x] == 0]
            x = rng.choice(missing)
            i = rng.randrange(k)
            j = rng.randrange(k)
            if i == j:
                continue
            y = (S[j] + x) % m
            if y in S:
                continue
            old = S[i]
            z = _move(S, cnt, i, y, m, zeros)
            delta = z - zeros
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                zeros = z
            else:
                _move(S, cnt, i, old, m, z)
        if zeros == 0:
            return sorted(S)
    return None


def _difference_graph(d, deadline, rng):
    """Largest cyclic Haar graph H(m, S) with |S| = d found before the deadline, as (n, edges), or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.4 * (deadline - now)))
        S = _cover_guided(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
        # Projective-plane arc extensions (the 394 family for d = 16).
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # New main search: guided difference-cover Haar graphs (diameter 3, valid for D >= 3).
        hg = _difference_graph(d, start + 0.80 * time_limit, rng)
        if hg is not None:
            consider(hg[0], hg[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
