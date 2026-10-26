#!/usr/bin/env python3
"""Card c01 builder.
  build.py pg Q            -> PG(2,Q) incidence graph (Q in 16,17,19), edge list on stdout
  build.py hat Q A C [f]   -> fourth-hat graph G(Q;a,c) (or R(Q;a,c) with the filler edges when f is given)
Edge list format: first line n, then 'u v' per line (the apsp.c input). Definitions follow
research/theorems/POLISHED.md section 2 (Definition 2.1, filler, Theorem 2.2)."""
import sys

class Field:
    def __init__(self, q):
        self.q = q
        if q == 16:  # GF(2)[x]/(x^4+x+1)
            def gmul(a, b):
                r = 0
                while b:
                    if b & 1:
                        r ^= a
                    b >>= 1
                    a <<= 1
                    if a & 16:
                        a ^= 0b10011
                return r
            self.ADD = [[a ^ b for b in range(q)] for a in range(q)]
            self.MUL = [[gmul(a, b) for b in range(q)] for a in range(q)]
        else:
            assert all(q % d for d in range(2, q)), "prime only (plus 16)"
            self.ADD = [[(a + b) % q for b in range(q)] for a in range(q)]
            self.MUL = [[(a * b) % q for b in range(q)] for a in range(q)]
        self.NEG = [next(b for b in range(q) if self.ADD[a][b] == 0) for a in range(q)]
        self.INV = [0] * q
        for a in range(1, q):
            self.INV[a] = next(b for b in range(1, q) if self.MUL[a][b] == 1)
        # field axioms spot check: distributivity and inverses
        for a in range(q):
            for b in range(q):
                for c in range(q):
                    assert self.MUL[a][self.ADD[b][c]] == self.ADD[self.MUL[a][b]][self.MUL[a][c]]
        for a in range(1, q):
            assert self.MUL[a][self.INV[a]] == 1
    def add(self, a, b): return self.ADD[a][b]
    def mul(self, a, b): return self.MUL[a][b]
    def neg(self, a): return self.NEG[a]
    def inv(self, a): return self.INV[a]
    def sub(self, a, b): return self.ADD[a][self.NEG[b]]
    def elems(self): return range(self.q)

def norm(F, v):
    """Normalise a projective coordinate vector: first nonzero entry becomes 1."""
    for x in v:
        if x != 0:
            i = F.inv(x)
            return tuple(F.mul(i, y) for y in v)
    raise ValueError("zero vector")

def pg_objects(F):
    q = F.q
    pts = set()
    for y in F.elems():
        for z in F.elems():
            pts.add(norm(F, (1, y, z)))
    for z in F.elems():
        pts.add(norm(F, (0, 1, z)))
    pts.add((0, 0, 1))
    assert len(pts) == q * q + q + 1
    return sorted(pts)

def dot(F, u, v):
    s = 0
    for a, b in zip(u, v):
        s = F.add(s, F.mul(a, b))
    return s

def pg_graph_edges(F):
    """Incidence pairs (point, line) of PG(2,q) as tuples of coordinates."""
    P = pg_objects(F)
    return [(p, L) for p in P for L in P if dot(F, p, L) == 0]

def pg_cmd(q):
    F = Field(q)
    E = pg_graph_edges(F)
    P = pg_objects(F)
    idx = {('pt', p): i for i, p in enumerate(P)}
    idx.update({('ln', L): len(P) + i for i, L in enumerate(P)})
    n = 2 * len(P)
    out = [f"{n}"] + [f"{idx[('pt', p)]} {idx[('ln', L)]}" for p, L in E]
    print("\n".join(out))

def hat_cmd(q, a, c, filler):
    F = Field(q)
    assert q >= 4 and a != c and a not in (0, 1) and c not in (0, 1)
    neg, inv, add = F.neg, F.inv, F.add
    FF = list(F.elems())
    S = [0, 1, a, c]
    T = [0, 1, c]
    sigma = {0: c, c: 1, 1: 0}          # (0 c 1): 0->c->1->0
    N = lambda *v: norm(F, v)
    PT = lambda v: ('pt', N(*v))
    LN = lambda v: ('ln', N(*v))
    A = PT((1, 0, 0))
    ell = LN((1, 0, 0))
    X = lambda t: PT((0, t, 1))
    P = PT((0, 1, 0))
    lam = lambda t: LN((0, 1, neg(t)))
    lam_inf = LN((0, 0, 1))
    Q = 'Q'
    H = lambda s: ('H', s)
    M = 'M'
    K = lambda s: ('K', s)

    pts_pg = pg_objects(F)
    lines_pg = pts_pg
    edges = set()
    def is_line(v):
        return v == 'M' or (isinstance(v, tuple) and v[0] in ('ln', 'K'))
    def add_edge(u, v):
        # orient every edge as (point, line)
        p, l = (v, u) if is_line(u) else (u, v)
        assert not is_line(p) and is_line(l), (u, v)
        key = (p, l)
        assert key not in edges, ("duplicate", key)
        edges.add(key)
    # (C1) plane incidences except X_s I lam_s (s in S), plus the rotation
    for p, L in pg_graph_edges(F):
        P_k, L_k = ('pt', p), ('ln', L)
        removed = False
        for s in S:
            if P_k == X(s) and L_k == lam(s):
                removed = True
        if not removed:
            add_edge(P_k, L_k)
    for t in T:
        add_edge(X(t), lam(sigma[t]))
    # (C2) H_s on [w:1:-s] for all w
    for s in S:
        for w in FF:
            add_edge(H(s), LN((w, 1, neg(s))))
    # (C3) K_s contains (x:s:1)
    for s in S:
        for x in FF:
            add_edge(K(s), PT((x, s, 1)))
    # (C4) M contains P, X_t (t not in T), H_0,H_1,H_a,H_c
    add_edge(M, P)
    for t in FF:
        if t not in T:
            add_edge(M, X(t))
    for s in S:
        add_edge(M, H(s))
    # (C5) Q on lam_inf, lam_t (t not in T), K_0,K_1,K_a,K_c
    add_edge(Q, lam_inf)
    for t in FF:
        if t not in T:
            add_edge(Q, lam(t))
    for s in S:
        add_edge(Q, K(s))
    # (C6) links
    add_edge(A, K(a))
    add_edge(H(a), ell)
    for t in T:
        add_edge(H(t), K(sigma[t]))
    # filler
    if filler:
        for x in FF:
            if x == 0:
                continue
            for y in FF:
                if y not in S:
                    add_edge(PT((x, y, 1)), LN((x, 1, neg(y))))
            add_edge(PT((x, 1, 0)), LN((1, 0, neg(inv(x)))))
    # vertex list
    points = [('pt', p) for p in pts_pg] + [Q] + [H(s) for s in S]
    lines = [('ln', L) for L in lines_pg] + [M] + [K(s) for s in S]
    n = len(points) + len(lines)
    assert len(points) == len(lines) == q * q + q + 6
    pid = {p: i for i, p in enumerate(points)}
    lid = {l: len(points) + i for i, l in enumerate(lines)}
    # every endpoint must be a known vertex, and edges must join a point and a line
    deg = {}
    for p, l in edges:
        assert p in pid and l in lid, (p, l)
        deg[p] = deg.get(p, 0) + 1
        deg[l] = deg.get(l, 0) + 1
    degs = [deg.get(v, 0) for v in points + lines]
    sys.stderr.write(f"q={q} a={a} c={c} filler={bool(filler)} n={n} edges={len(edges)} "
                     f"deg min={min(degs)} max={max(degs)}\n")
    out = [f"{n}"] + [f"{pid[p]} {lid[l]}" for p, l in sorted(edges, key=lambda e: (pid[e[0]], lid[e[1]]))]
    print("\n".join(out))

if __name__ == "__main__":
    if sys.argv[1] == "pg":
        pg_cmd(int(sys.argv[2]))
    elif sys.argv[1] == "hat":
        hat_cmd(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), len(sys.argv) > 5)
    else:
        raise SystemExit(__doc__)
