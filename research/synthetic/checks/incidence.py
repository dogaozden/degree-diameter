"""Small helpers shared by the checks of SYNTHETIC.tex, Sections 2 and 3.

An incidence structure is given by a list of points, a list of lines and a set of flags (p, L);
elements are arbitrary hashable names.  Nothing here uses coordinates: the classical geometries
are built from coordinates in the check scripts, and then only their incidence is used.
"""
import itertools
from collections import defaultdict


class Structure:
    def __init__(self, points, lines, flags):
        self.points = list(points)
        self.lines = list(lines)
        self.flags = set(flags)
        self.lines_on = defaultdict(set)
        self.pts_on = defaultdict(set)
        for p, L in self.flags:
            self.lines_on[p].add(L)
            self.pts_on[L].add(p)
        assert len(set(self.points)) == len(self.points) and len(set(self.lines)) == len(self.lines)
        assert not (set(self.points) & set(self.lines))

    def deg(self, x):
        return len(self.lines_on[x]) if x in self.lines_on or x in set(self.points) else len(self.pts_on[x])

    def point_degree(self, p):
        return len(self.lines_on[p])

    def line_degree(self, L):
        return len(self.pts_on[L])

    def collinear(self, u, v):
        return bool(self.lines_on[u] & self.lines_on[v])

    def nbrs(self, x):
        return self.lines_on[x] if x in self._ptset else self.pts_on[x]

    @property
    def _ptset(self):
        if not hasattr(self, '_ps'):
            self._ps = set(self.points)
        return self._ps

    def adjacency_bits(self):
        names = self.points + self.lines
        idx = {v: i for i, v in enumerate(names)}
        adj = [0] * len(names)
        for p, L in self.flags:
            i, j = idx[p], idx[L]
            adj[i] |= 1 << j
            adj[j] |= 1 << i
        return names, idx, adj

    def diameter(self):
        """Exact diameter of the incidence graph (None if disconnected), bitset BFS from every vertex."""
        names, idx, adj = self.adjacency_bits()
        n = len(names)
        full = (1 << n) - 1
        best = 0
        for v in range(n):
            ball = frontier = 1 << v
            r = 0
            while ball != full:
                nxt = 0
                b = frontier
                while b:
                    low = b & -b
                    nxt |= adj[low.bit_length() - 1]
                    b ^= low
                frontier = nxt & ~ball
                if not frontier:
                    return None
                ball |= nxt
                r += 1
            best = max(best, r)
        return best

    def distances_from(self, src):
        names, idx, adj = self.adjacency_bits()
        dist = {src: 0}
        frontier = [src]
        while frontier:
            nxt = []
            for x in frontier:
                for y in self.nbrs(x):
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        nxt.append(y)
            frontier = nxt
        return dist


def is_gq(S, s, t):
    """Order (s,t) and: for every anti-flag (p, L) exactly one point of L is collinear with p."""
    if any(len(S.pts_on[L]) != s + 1 for L in S.lines):
        return False
    if any(len(S.lines_on[p]) != t + 1 for p in S.points):
        return False
    for p in S.points:
        coll = set()
        for L in S.lines_on[p]:
            coll |= S.pts_on[L]
        for L in S.lines:
            if p in S.pts_on[L]:
                continue
            if len(S.pts_on[L] & coll) != 1:
                return False
    return True


# ------------------------------------------------------------------ W(3,q) for q prime

def proj_points(q, n):
    pts = []
    for v in itertools.product(range(q), repeat=n):
        if any(v):
            i = next(i for i in range(n) if v[i])
            if v[i] == 1:
                pts.append(v)
    return pts


def symplectic_W3(q):
    """W(3,q), q prime, form b(u,v) = u0v1 - u1v0 + u2v3 - u3v2.  Points: tuples; lines: frozensets."""
    pts = proj_points(q, 4)

    def b(u, v):
        return (u[0] * v[1] - u[1] * v[0] + u[2] * v[3] - u[3] * v[2]) % q

    def norm(v):
        i = next(i for i in range(4) if v[i] % q)
        inv = pow(v[i], q - 2, q)
        return tuple((x * inv) % q for x in v)

    lines = set()
    for u, v in itertools.combinations(pts, 2):
        if b(u, v) == 0:
            L = frozenset({u, v} | {norm(tuple((a * x + y) % q for x, y in zip(u, v))) for a in range(q)})
            lines.add(L)
    lines = sorted(lines, key=lambda L: sorted(L))
    names = [('W', i) for i in range(len(lines))]
    flags = {(p, names[i]) for i, L in enumerate(lines) for p in L}
    return Structure(pts, names, flags), b


def payne_derivation(W, x):
    """P(W, x): points = points not collinear with x (and != x); lines = lines of W not through x,
    minus their unique point collinear with x; and the sets {x,y}^{perp perp} minus x, y not collinear
    with x.  Uses only incidence."""
    perp = {}
    for p in W.points:
        s = set()
        for L in W.lines_on[p]:
            s |= W.pts_on[L]
        perp[p] = s           # p together with the points collinear with p
    xp = perp[x]
    pts = [p for p in W.points if p not in xp]
    lines, flags = [], set()
    for L in W.lines:
        if x in W.pts_on[L]:
            continue
        name = ('old', L)
        lines.append(name)
        for p in W.pts_on[L]:
            if p not in xp:
                flags.add((p, name))
    seen = set()
    for y in pts:
        span = set(W.points)
        common = xp & perp[y]          # {x,y}^perp
        for z in common:
            span &= perp[z]            # {x,y}^{perp perp}
        hyp = frozenset(span - {x})
        if hyp in seen:
            continue
        seen.add(hyp)
        name = ('hyp', len(seen))
        lines.append(name)
        for p in hyp:
            flags.add((p, name))
    return Structure(pts, lines, flags)


# ------------------------------------------------------------------ Delorme's doubling with levels

def double_levels(S, level, m):
    """level: dict element -> level >= 0 (elements absent have level -1).  Versions x^w, w a word over
    range(m) of length level(x)+1; x^w I y^u iff x I y and w, u comparable (one a prefix of the other).
    Returns the doubled Structure; versions are named (x, w) with w a tuple (() for level -1)."""
    def versions(x):
        k = level.get(x, -1)
        return [(x, w) for w in itertools.product(range(m), repeat=k + 1)]

    def comparable(w, u):
        n = min(len(w), len(u))
        return w[:n] == u[:n]

    pts = [v for p in S.points for v in versions(p)]
    lns = [v for L in S.lines for v in versions(L)]
    flags = set()
    for p, L in S.flags:
        for vp in versions(p):
            for vl in versions(L):
                if comparable(vp[1], vl[1]):
                    flags.add((vp, vl))
    return Structure(pts, lns, flags)
