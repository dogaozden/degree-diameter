import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Main new construction: cyclic Haar graphs from difference covers.
#
# For B a subset of Z_v with |B| = d, the Haar graph H(Z_v, B) is d-regular and
# bipartite on 2v vertices (point i ~ block j iff j - i is in B). It has
# diameter <= 3 whenever every nonzero residue of Z_v is a difference b - b'
# with b, b' in B (a difference cover). Cross pairs then follow because
# x = (x - b') + b' for any b' in B with x != b'.
#
# Search: simulated annealing over d-subsets of Z_v, minimising the number of
# uncovered nonzero residues. We climb v upward from a feasible-looking start
# and keep the largest v that succeeds. The record 394 corresponds to v = 197;
# any success at v >= 198 beats it.
#
# Fallback: the arc-extended projective plane graphs from the parent program
# (order 394 at d = 16), then K_{d,d}. Every candidate is checked with
# lib.is_valid before it can be returned.
# ----------------------------------------------------------------------------


def _swap(cnt, others, old, new, v):
    """Remove difference contributions of `old` and add those of `new` against `others`.

    cnt[x] counts ordered differences b - c (b != c, both in B) that equal x.
    Returns the change in the number of uncovered nonzero residues.
    """
    ch = 0
    for c in others:
        a = (old - c) % v
        cnt[a] -= 1
        if cnt[a] == 0:
            ch += 1
        a = (c - old) % v
        cnt[a] -= 1
        if cnt[a] == 0:
            ch += 1
    for c in others:
        a = (new - c) % v
        if cnt[a] == 0:
            ch -= 1
        cnt[a] += 1
        a = (c - new) % v
        if cnt[a] == 0:
            ch -= 1
        cnt[a] += 1
    return ch


def _cover_search(v, k, rng, deadline):
    """Find B in Z_v with |B| = k, 0 in B, whose differences cover all nonzero residues. None on timeout."""
    if k > v:
        return None
    B = [0] + rng.sample(range(1, v), k - 1)
    inB = [False] * v
    for b in B:
        inB[b] = True
    cnt = [0] * v
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(B[i] - B[j]) % v] += 1
    unc = sum(1 for x in range(1, v) if cnt[x] == 0)
    if unc == 0:
        return B
    T = 0.4
    it = 0
    while True:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)          # B[0] = 0 stays fixed
        x = rng.randrange(1, v)
        if inB[x]:
            continue
        old = B[i]
        others = B[:i] + B[i + 1:]
        ch = _swap(cnt, others, old, x, v)
        if ch <= 0 or rng.random() < math.exp(-ch / T):
            B[i] = x
            inB[old] = False
            inB[x] = True
            unc += ch
            if unc == 0:
                return B
        else:
            _swap(cnt, others, x, old, v)  # revert


def _cyclic(d, rng, deadline):
    """Climb v upward from a feasible-looking start; return (v, B) for the largest success, or None."""
    if d < 3:
        return None
    vcap = d * d - d + 1  # cyclic difference-cover bound: d(d-1) ordered differences
    v = max(d, int(0.8 * vcap))
    best = None
    while time.monotonic() < deadline and d <= v <= vcap:
        now = time.monotonic()
        remaining = deadline - now
        frac = 0.35 if best is None else 0.5
        end = min(deadline, now + remaining * frac)
        B = _cover_search(v, d, rng, end)
        if B is not None:
            best = (v, B)
            v += 1
        elif best is not None:
            break
        else:
            v -= 1
    return best


# ----------------------------------------------------------------------------
# Parent fallback: arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

_LP = None  # line_points for the current q, set in _arc_extensions


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, w in edges:
        point_lines[u].append(w - m)
        line_points[w - m].append(u)
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


def _arc_graph(m, edges, point_lines, S):
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
        for Q in _LP[j]:
            E.append((Q, b))
    return n, E


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree <= d."""
    E = set()
    for u, w in edges:
        E.add((u, w) if u < w else (w, u))
    deg = [0] * n
    for u, w in E:
        deg[u] += 1
        deg[w] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    global _LP
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        _LP = line_points
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S)
        n_c, e_c = _saturate(n_c, e_c, m, len(S), d, rng)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3 and d >= 3:
        # Parent's arc-extended graphs (order 394 at d = 16): a strong fallback.
        arc_deadline = start + 0.2 * total
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

        # Bold new construction: cyclic Haar graph of a difference cover.
        res = _cyclic(d, rng, deadline)
        if res is not None:
            v, B = res
            n_c, e_c = lib.haar_graph(v, B)
            consider(n_c, e_c)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
