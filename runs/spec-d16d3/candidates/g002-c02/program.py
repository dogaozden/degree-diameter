import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold construction: greedy "cover" extension of projective-plane incidence graphs.
#
# State: a bipartite graph with max degree d and diameter <= 3 (checked by
# construction). A new vertex x of type c with neighbour set N (all of the
# opposite type, all with spare degree) keeps diameter 3 exactly when the
# neighbourhoods of N together cover every existing vertex of type c. Then:
#   - type-c vertices are at distance 2 from x,
#   - type-(1-c) vertices are at distance 1 (if in N) or 3 (via a covered type-c vertex),
# and every earlier pair keeps its distance (adding vertices never lengthens paths).
# So growth is sound by construction; lib.is_valid is still run on every candidate.
#
# Starts: PG(2,q) incidence graphs for the largest prime powers q < d, and the
# conic/hyperoval-extended graph (the parent's construction) when it fits.
# Greedy set-cover with random tie-breaks adds vertices while capacity remains.
# Fallbacks: K_{d,d} (diameter 2), C_{2D} for d = 2, K_2 for d = 1.
# ----------------------------------------------------------------------------


def _pc(x):
    return x.bit_count()


class _State:
    """Bipartite graph under incremental growth, with bitmask neighbourhoods."""

    def __init__(self, d, n, edges, color):
        self.d = d
        self.n = n
        self.color = list(color)
        self.edges = list(edges)
        self.deg = [0] * n
        self.nb = [0] * n
        for u, v in self.edges:
            self.deg[u] += 1
            self.deg[v] += 1
            self.nb[u] |= 1 << v
            self.nb[v] |= 1 << u
        self.typemask = [0, 0]
        for v in range(n):
            self.typemask[self.color[v]] |= 1 << v

    def cover(self, c, rng):
        """Choose <= d opposite-type vertices with spare degree whose neighbourhoods cover all type-c vertices."""
        d = self.d
        unc = self.typemask[c]
        cand = [v for v in range(self.n) if self.color[v] != c and self.deg[v] < d]
        chosen = []
        while unc:
            if len(chosen) >= d:
                return None
            best = -1
            best_key = None
            for v in cand:
                g = _pc(self.nb[v] & unc)
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best = v
            if best < 0:
                return None
            chosen.append(best)
            unc &= ~self.nb[best]
            cand.remove(best)
        return chosen

    def add(self, c, nbrs):
        x = self.n
        self.n += 1
        self.color.append(c)
        mask = 0
        for v in nbrs:
            mask |= 1 << v
            self.nb[v] |= 1 << x
            self.deg[v] += 1
            self.edges.append((v, x))
        self.nb.append(mask)
        self.deg.append(len(nbrs))
        self.typemask[c] |= 1 << x


def _grow(st, rng, deadline, tries=25, max_fail=60):
    """Repeatedly add vertices whose covers exist, until time runs out or progress stalls."""
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        c = rng.randrange(2)
        chosen = None
        for _ in range(tries):
            chosen = st.cover(c, rng)
            if chosen is not None:
                break
        if chosen is None:
            fails += 1
        else:
            st.add(c, chosen)
            fails = 0


def _pg(q):
    """Incidence graph of PG(2,q): points 0..m-1, lines m..2m-1; also the point vectors."""
    n2, edges = lib.projective_plane_incidence(q)
    return n2 // 2, edges, lib.projective_points(q)


def _conic_start(d, q, m, edges, pts):
    """Parent's arc extension (conic, plus nucleus for even q). Returns (n, edges, color) or None."""
    s = d - q - 1
    if s < 2:
        return None
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])

    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)

    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return None

    E = list(edges)
    color = [0] * m + [1] * m
    n = 2 * m
    for P in S:
        x = n
        n += 1
        color.append(0)
        for L in point_lines[P]:
            E.append((x, m + L))
    for j in S:
        b = n
        n += 1
        color.append(1)
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, color


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    # D >= 3: diameter-3 constructions below are valid for every D >= 3.
    qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)[:4]
    starts = []
    for q in qs:
        m, edges, pts = _pg(q)
        cs = _conic_start(d, q, m, edges, pts)
        if cs is not None:
            starts.append(cs)
        starts.append((2 * m, edges, [0] * m + [1] * m))

    rng = random.Random(seed * 1000003 + d * 97 + D)
    for idx, (n0, e0, col) in enumerate(starts):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(starts) - idx)
        st = _State(d, n0, e0, col)
        _grow(st, rng, now + share)
        if st.n > best_n and lib.is_valid(st.n, st.edges, d, D):
            best_n, best_e = st.n, list(st.edges)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
