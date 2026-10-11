import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base with independent arc extensions (diameter 3).
#
# Points are 0..m-1 and lines m..2m-1 in the incidence graph of PG(2, q).
# Old vertices have degree q+1, so spare capacity is s = d - q - 1 per vertex.
# A set SA of points gets new "A" vertices, each joined to the q+1 lines
# through its point. A set SB of lines gets new "B" vertices, each joined to
# the q+1 points on its line. Both sets must be s-bounded: every line carries
# at most s points of SA, and every point lies on at most s lines of SB.
# SA and SB are chosen independently (greedy or conic).
#
# NEW: greedy augmentation by cover. After the base is built, repeatedly add a
# new vertex X on one side, joined to a set T of existing vertices on the other
# side with spare degree. A valid T is one whose radius-(D-1) balls cover every
# vertex. This is exact: X reaches v within D iff some t in T has dist(t, v) <= D-1.
# Adding vertices never increases existing distances, so validity is preserved.
# Candidates are chosen by randomized max-coverage greedy; BFS bitsets do the checks.
# ----------------------------------------------------------------------------


def _incidence(q):
    """Return (m, pl, lp): pl[P] = lines through point P, lp[L] = points on line L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, pl, lp


def _pg_data(q):
    """Return (m, pl, lp, conic) for PG(2, q), where conic is an arc of q+1 (or q+2) indices."""
    m, pl, lp = _incidence(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        conic.append(index[(0, 1, 0)])
    return m, pl, lp, conic


def _loads_ok(S, inc, m, s):
    """True if no target is hit more than s times by the incidence lists inc[i] for i in S."""
    load = [0] * m
    for i in S:
        for t in inc[i]:
            load[t] += 1
            if load[t] > s:
                return False
    return True


def _greedy(inc, m, s, rng, trials, deadline):
    """Randomized greedy s-bounded set; returns the largest found over the trials."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for i in order:
            ts = inc[i]
            if all(load[t] < s for t in ts):
                S.append(i)
                for t in ts:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc(inc, m, s, rng, deadline, conic):
    """Largest of a greedy s-bounded set and the conic set, when the conic is valid."""
    cands = [_greedy(inc, m, s, rng, 25, deadline)]
    if conic and _loads_ok(conic, inc, m, s):
        cands.append(conic)
    return max(cands, key=len)


def _base(q, d, data, rng, deadline):
    """Build the PG(2,q) incidence graph plus A and B extension vertices. Returns (n, edges)."""
    m, pl, lp, conic = data
    s = d - q - 1
    SA = _arc(pl, m, s, rng, deadline, conic)
    SB = _arc(lp, m, s, rng, deadline, conic)
    n = 2 * m
    edges = []
    for P in range(m):
        for L in pl[P]:
            edges.append((P, m + L))
    for P in SA:
        a = n
        n += 1
        for L in pl[P]:
            edges.append((a, m + L))
    for j in SB:
        b = n
        n += 1
        for Q in lp[j]:
            edges.append((Q, b))
    return n, edges


def _two_color(nb, n):
    """Return a 2-colouring of a bipartite adjacency list."""
    col = [-1] * n
    for s0 in range(n):
        if col[s0] != -1:
            continue
        col[s0] = 0
        stack = [s0]
        while stack:
            u = stack.pop()
            for v in nb[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _ball(nb, n, R):
    """Bitmask of all vertices within distance R, per vertex."""
    cur = [1 << v for v in range(n)]
    for _ in range(R):
        nxt = []
        for v in range(n):
            x = cur[v]
            for u in nb[v]:
                x |= cur[u]
            nxt.append(x)
        cur = nxt
    return cur


def _cover(cand, ball, full, d, rng):
    """Greedy max-coverage: pick up to d vertices from cand whose balls cover full. None on failure."""
    uncovered = full
    chosen = []
    used = set()
    pool = list(cand)
    rng.shuffle(pool)
    while uncovered:
        if len(chosen) >= d:
            return None
        best = None
        bkey = None
        for t in pool:
            if t in used:
                continue
            g = (ball[t] & uncovered).bit_count()
            if g == 0:
                continue
            key = (g, rng.random())
            if bkey is None or key > bkey:
                bkey = key
                best = t
        if best is None:
            return None
        used.add(best)
        chosen.append(best)
        uncovered &= ~ball[best]
    return chosen


def _augment(n, edges, d, D, rng, deadline, stall):
    """Greedily add new vertices by cover while the graph stays valid. Returns (n, adjacency)."""
    nb = [[] for _ in range(n)]
    for u, v in edges:
        nb[u].append(v)
        nb[v].append(u)
    side = _two_color(nb, n)
    ball = _ball(nb, n, D - 1)
    fails = 0
    want = 0
    while fails < stall and time.monotonic() < deadline:
        want ^= 1
        cand = [t for t in range(n) if side[t] == 1 - want and len(nb[t]) < d]
        T = _cover(cand, ball, (1 << n) - 1, d, rng)
        if T is None:
            fails += 1
            continue
        x = n
        n += 1
        nb.append(list(T))
        side.append(want)
        for t in T:
            nb[t].append(x)
        ball = _ball(nb, n, D - 1)
        fails = 0
    return n, nb


def _to_edges(nb):
    return [(u, v) for u in range(len(nb)) for v in nb[u] if u < v]


def _search(d, D, seed, deadline):
    """Repeat: random base for the largest few q, augment by cover, keep the best valid graph."""
    rng = random.Random(seed)
    qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)[:3]
    if not qs:
        return None
    data = {q: _pg_data(q) for q in qs}
    best = None
    bn = 0
    stale = 0
    while time.monotonic() < deadline and stale < 300:
        improved = False
        for q in qs:
            if time.monotonic() >= deadline:
                break
            n, E = _base(q, d, data[q], rng, deadline)
            n, nb = _augment(n, E, d, D, rng, deadline, 40)
            if n > bn:
                E2 = _to_edges(nb)
                if lib.is_valid(n, E2, d, D):
                    best = (n, E2)
                    bn = n
                    improved = True
        stale = 0 if improved else stale + 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.6 * time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    try:
        if D >= 3:
            res = _search(d, D, seed, deadline)
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                best_n, best_e = res

        if D >= 4 and d >= 3 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None and gq[0] > best_n and lib.is_valid(gq[0], gq[1], d, D):
                best_n, best_e = gq
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
