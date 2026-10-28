"""Explicit hub graphs (classes A, B; max degree <= delta; same-colour distance <= 4).

Building blocks (all deterministic):
  pg(s)      incidence graph of PG(2,s), s a prime power (points = A, lines = B)
  gq(q)      incidence graph of the symplectic GQ W(q) (points = A, lines = B), order (q,q)
  pendant windows: attach extra degree-1 vertices ("pendants") to core vertices.

Pendant rules (proved in construction.md, checked by BFS):
  * a pendant on an A-vertex is a B-vertex; a pendant on a B-vertex is an A-vertex.
  * the pendants on one side may sit only on a set S of vertices that are pairwise at distance <= 2
    in the core, and every vertex of S must be within distance 3 of every core vertex of the other class.
    In PG(2,s) every set of points (and every set of lines) qualifies; in a GQ only the points of one line
    (or the lines through one point) qualify.
"""
import itertools, random

# ---------- finite fields ----------
def _factor_prime_power(q):
    for p in range(2, q + 1):
        if q % p == 0:
            k, t = 0, q
            while t % p == 0:
                t //= p; k += 1
            assert t == 1, "not a prime power"
            return p, k
    raise ValueError

def _poly_mul_mod(a, b, mod, p, k):
    # a, b: lists of length k (coeffs low->high); mod: monic degree-k poly as list length k+1
    res = [0] * (2 * k - 1) if k > 0 else [0]
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b):
            res[i + j] = (res[i + j] + x * y) % p
    for d in range(len(res) - 1, k - 1, -1):
        c = res[d]
        if c:
            for t in range(k + 1):
                res[d - k + t] = (res[d - k + t] - c * mod[t]) % p
    return res[:k]

def field(q):
    """Return (add, mul, neg) tables for GF(q), elements 0..q-1 (0 = zero, 1 = one)."""
    p, k = _factor_prime_power(q)
    if k == 1:
        add = [[(a + b) % p for b in range(q)] for a in range(q)]
        mul = [[(a * b) % p for b in range(q)] for a in range(q)]
    else:
        # find irreducible monic poly of degree k over F_p
        def to_vec(x):
            return [(x // p ** i) % p for i in range(k)]
        def to_int(v):
            return sum(c * p ** i for i, c in enumerate(v))
        for coeffs in itertools.product(range(p), repeat=k):
            mod = list(coeffs) + [1]
            # irreducible iff no roots and (for k<=3) no roots suffices; for k=2,3 check no nontrivial factor
            ok = True
            for r in range(p):
                if sum(mod[i] * r ** i for i in range(k + 1)) % p == 0:
                    ok = False; break
            if ok and k == 4:
                # check no quadratic factor (not needed here)
                pass
            if ok:
                break
        add = [[to_int([(x + y) % p for x, y in zip(to_vec(a), to_vec(b))]) for b in range(q)] for a in range(q)]
        mul = [[to_int(_poly_mul_mod(to_vec(a), to_vec(b), mod, p, k)) for b in range(q)] for a in range(q)]
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [None] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    return add, mul, neg, inv

# ---------- projective geometry ----------
def _normalized(vecs_iter, F):
    add, mul, neg, inv = F
    pts = []
    return pts

def proj_points(dim, q):
    """All normalized vectors of length dim over GF(q) (first nonzero coordinate = 1)."""
    out = []
    for v in itertools.product(range(q), repeat=dim):
        nz = [c for c in v if c != 0]
        if nz and nz[0] == 1:
            out.append(v)
    return out

def pg2(s):
    """PG(2,s) incidence. Returns (N, incid) where incid[i] = list of line indices through point i ...
    We return point_lines[p] (lines through p) and line_points[l]."""
    F = field(s)
    add, mul, neg, inv = F
    P = proj_points(3, s)
    idx = {v: i for i, v in enumerate(P)}
    def dot(u, v):
        t = 0
        for a, b in zip(u, v):
            t = add[t][mul[a][b]]
        return t
    line_points = [[i for i, p in enumerate(P) if dot(l, p) == 0] for l in P]
    return len(P), line_points

def gq_w(q):
    """Symplectic GQ W(q): points of PG(3,q), lines = totally isotropic lines.
    Returns (N, line_points) with N = (q+1)(q^2+1) points, and N lines."""
    F = field(q)
    add, mul, neg, inv = F
    P = proj_points(4, q)
    def B(u, v):
        # x0 y1 - x1 y0 + x2 y3 - x3 y2 (signs irrelevant in char 2)
        t1 = add[mul[u[0]][v[1]]][neg[mul[u[1]][v[0]]]]
        t2 = add[mul[u[2]][v[3]]][neg[mul[u[3]][v[2]]]]
        return add[t1][t2]
    n = len(P)
    orth = [[j for j in range(n) if B(P[i], P[j]) == 0 and j != i] for i in range(n)]
    def span_norm(u, v):
        pts = set()
        for a in range(q):
            for b in range(q):
                if a == 0 and b == 0: continue
                w = tuple(add[mul[a][x]][mul[b][y]] for x, y in zip(u, v))
                nz = [c for c in w if c != 0]
                if nz and nz[0] == 1:
                    pts.add(w)
        return frozenset(P.index(x) for x in pts)
    lines = set()
    for i in range(n):
        for j in orth[i]:
            L = span_norm(P[i], P[j])
            if len(L) == q + 1:
                lines.add(L)
    lines = sorted(sorted(L) for L in lines)
    assert len(lines) == (q + 1) * (q * q + 1), (len(lines), q)
    return n, lines

# ---------- graph assembly ----------
class Graph:
    """Vertices: A (colour 0) and B (colour 1) are created on demand."""
    def __init__(self):
        self.col = []
        self.edges = []
    def add(self, c):
        self.col.append(c)
        return len(self.col) - 1
    def edge(self, u, v):
        assert self.col[u] != self.col[v]
        self.edges.append((u, v))
    def degrees(self):
        d = [0] * len(self.col)
        for u, v in self.edges:
            d[u] += 1; d[v] += 1
        return d
    def write(self, path, comment=""):
        with open(path, "w") as f:
            f.write(f"{len(self.col)} {len(self.edges)}\n")
            for u, v in self.edges:
                f.write(f"{u} {v}\n")
        return path

def core_pg(G, s):
    """Add PG(2,s) incidence; return (points, lines) as vertex id lists."""
    N, lp = pg2(s)
    pts = [G.add(0) for _ in range(N)]
    lns = [G.add(1) for _ in range(N)]
    for l, plist in enumerate(lp):
        for p in plist:
            G.edge(pts[p], lns[l])
    return pts, lns, lp

def pg_window_graph(s, KA, KB, delta):
    """PG(2,s) + pendants: KA = #A-vertices, KB = #B-vertices. Requires N <= KA, KB <= N*(delta-s)."""
    N, lp = pg2(s)
    G = Graph()
    pts, lns, _ = core_pg(G, s)
    cap = delta - s - 1
    addB = KB - N   # pendants on points (become B)
    addA = KA - N   # pendants on lines (become A)
    assert 0 <= addB <= N * cap and 0 <= addA <= N * cap
    for i in range(addB):
        G.edge(pts[i % N], G.add(1))
    for i in range(addA):
        G.edge(lns[i % N], G.add(0))
    return G

def gq_window_graph(q, KA, KB, delta):
    """W(q) + pendants on the q+1 points of one line (B pendants) and the q+1 lines through one point (A pendants)."""
    N, lines = gq_w(q)
    G = Graph()
    pts = [G.add(0) for _ in range(N)]
    lns = [G.add(1) for _ in range(N)]
    for l, plist in enumerate(lines):
        for p in plist:
            G.edge(pts[p], lns[l])
    # line 0 = L; point x0 = a point on line 0; lines through x0
    L_points = lines[0]
    x0 = L_points[0]
    through_x0 = [l for l, pl in enumerate(lines) if x0 in pl]
    cap = delta - (q + 1)
    addB, addA = KB - N, KA - N
    assert 0 <= addB <= (q + 1) * cap and 0 <= addA <= (q + 1) * cap, (addB, addA)
    for i in range(addB):
        G.edge(pts[L_points[i % (q + 1)]], G.add(1))
    for i in range(addA):
        G.edge(lns[through_x0[i % (q + 1)]], G.add(0))
    return G
