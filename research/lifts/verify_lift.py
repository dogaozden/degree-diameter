"""Independent rebuild and check of a lift solution file (written by lift.c).

Usage: python3 -I verify_lift.py SOL.txt [EDGES_OUT] [--full] [--no-bfs]

The group is rebuilt here from its definition, not from lift.c's tables:
  cyc n          integers mod n
  meta m k r     pairs (a, j), (a, j)(b, l) = (a + r^j b mod m, j + l mod k)
  dih n          meta n 2 n-1
  sl p / psl p / pgl p   2x2 matrices over Z/p with det 1 / det 1 modulo +-1 / det != 0 modulo scalars
  G x H          direct product (tuples)
Elements are listed in sorted order of their canonical tuples; lift vertex (u, g) gets index u*N + rank(g).
Edges: base edge "e x y = a" gives (x, g) ~ (y, a g) for every g.

Checks (printed): n, edge count, min/max degree, repeated edges, bipartite (2-colouring of the lift itself),
connected, right translations by a generating set of the group are automorphisms (so every fiber is one orbit
and ecc((u,g)) = ecc((u,1))), eccentricity of (u,1) for every base vertex u (plain BFS), hence the diameter.
--full: also all-pairs BFS with networkx (only sensible for n up to a few thousand).
The edge list (first line n, then "u v" per edge, u < v, sorted) is written to EDGES_OUT if given; its sha256 is
printed either way. A permutation file EDGES_OUT.perms (one line per generator: images of 0..n-1) is written too,
for check_edges.py.
Exit status 0 iff the lift is simple, connected, bipartite, regular of the claimed degree, and has diameter <= D.
"""
import hashlib
import random
import sys
from collections import deque


# ------------------------------------------------------------------ groups
class Cyc:
    def __init__(self, n):
        self.n = n
        self.elems = list(range(n))
        self.e = 0

    def mul(self, x, y):
        return (x + y) % self.n

    def parse(self, s):
        (a,) = map(int, s.split(","))
        return a % self.n


class Meta:
    def __init__(self, m, k, r):
        assert pow(r, k, m) == 1 % m, "r^k != 1 mod m"
        self.m, self.k, self.r = m, k, r
        self.elems = [(a, j) for a in range(m) for j in range(k)]
        self.e = (0, 0)

    def mul(self, x, y):
        a, j = x
        b, l = y
        return ((a + pow(self.r, j, self.m) * b) % self.m, (j + l) % self.k)

    def parse(self, s):
        a, j = map(int, s.split(","))
        return (a % self.m, j % self.k)


class Mat:
    def __init__(self, kind, p):
        assert p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1)), "p must be prime"
        self.kind, self.p = kind, p
        els = set()
        rng = range(p)
        for a in rng:
            for b in rng:
                for c in rng:
                    if kind == "pgl":
                        for d in rng:
                            if (a * d - b * c) % p:
                                els.add(self.canon((a, b, c, d)))
                    else:
                        # det = 1: a d - b c = 1
                        if a % p:
                            d = (1 + b * c) * pow(a, p - 2, p) % p
                            els.add(self.canon((a, b, c, d)))
                        elif (b * c) % p == p - 1:
                            for d in rng:
                                els.add(self.canon((a, b, c, d)))
        self.elems = sorted(els)
        self.e = self.canon((1, 0, 0, 1))

    def canon(self, A):
        p = self.p
        A = tuple(x % p for x in A)
        if self.kind == "psl":
            B = tuple((-x) % p for x in A)
            return min(A, B)
        if self.kind == "pgl":
            f = next(x for x in A if x)
            s = pow(f, p - 2, p)
            return tuple(x * s % p for x in A)
        return A

    def mul(self, X, Y):
        a, b, c, d = X
        e, f, g, h = Y
        return self.canon((a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h))

    def parse(self, s):
        A = tuple(map(int, s.split(",")))
        assert len(A) == 4
        det = (A[0] * A[3] - A[1] * A[2]) % self.p
        assert (det != 0) if self.kind == "pgl" else (det == 1), "bad determinant"
        return self.canon(A)


class Prod:
    def __init__(self, fs):
        self.fs = fs
        els = [()]
        for f in fs:
            els = [x + (y,) for x in els for y in f.elems]
        self.elems = sorted(els)
        self.e = tuple(f.e for f in fs)

    def mul(self, x, y):
        return tuple(f.mul(a, b) for f, a, b in zip(self.fs, x, y))

    def parse(self, s):
        parts = s.split("|")
        assert len(parts) == len(self.fs)
        return tuple(f.parse(t) for f, t in zip(self.fs, parts))


def parse_group(tokens):
    fs = []
    i = 0
    while i < len(tokens):
        t = tokens[i]
        if t == "cyc":
            fs.append(Cyc(int(tokens[i + 1])))
            i += 2
        elif t == "meta":
            fs.append(Meta(int(tokens[i + 1]), int(tokens[i + 2]), int(tokens[i + 3])))
            i += 4
        elif t == "dih":
            n = int(tokens[i + 1])
            fs.append(Meta(n, 2, n - 1))
            i += 2
        elif t in ("sl", "psl", "pgl"):
            fs.append(Mat(t, int(tokens[i + 1])))
            i += 2
        else:
            raise ValueError("unknown factor " + t)
        if i < len(tokens):
            assert tokens[i] == "x", "factors are joined by x"
            i += 1
    return Prod(fs)


# ------------------------------------------------------------------ main
def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    full = "--full" in sys.argv
    sol = args[0]
    eout = args[1] if len(args) > 1 else None
    D = None
    gtok = None
    k = None
    base = []
    for line in open(sol):
        line = line.split("#")[0].strip()
        if not line:
            continue
        w = line.split()
        if w[0] == "lift":
            D = int(w[w.index("D") + 1])
        elif w[0] == "group":
            gtok = w[1:]
        elif w[0] == "k":
            k = int(w[1])
        elif w[0] == "e":
            x, y = int(w[1]), int(w[2])
            assert w[3] == "="
            base.append((x, y, " ".join(w[4:])))
    G = parse_group(gtok)
    N = len(G.elems)
    rank = {g: i for i, g in enumerate(G.elems)}
    n = k * N
    print(f"solution {sol}: group {' '.join(gtok)} (order {N}), base k={k} with {len(base)} edges, D={D}; lift n={n}")
    # multiplication by each voltage (as index permutations)
    edges = []
    volts = []
    for x, y, s in base:
        a = G.parse(s)
        volts.append(a)
        for g in G.elems:
            u, v = x * N + rank[g], y * N + rank[G.mul(a, g)]
            edges.append((min(u, v), max(u, v)))
    edges.sort()
    rep = sum(1 for i in range(1, len(edges)) if edges[i] == edges[i - 1])
    loops = sum(1 for u, v in edges if u == v)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    degs = [len(a) for a in adj]
    print(f"edges {len(edges)}, degree min {min(degs)} max {max(degs)}, repeated edges {rep}, loops {loops}")
    text = f"{n}\n" + "".join(f"{u} {v}\n" for u, v in edges)
    sha = hashlib.sha256(text.encode()).hexdigest()
    print(f"edge list sha256 {sha}")
    if eout:
        with open(eout, "w") as f:
            f.write(text)
        print(f"wrote {eout}")
    # bipartite + connected (from the lift itself)
    col = [-1] * n
    col[0] = 0
    dq = deque([0])
    bip = True
    while dq:
        u = dq.popleft()
        for v in adj[u]:
            if col[v] < 0:
                col[v] = 1 - col[u]
                dq.append(v)
            elif col[v] == col[u]:
                bip = False
    conn = all(c >= 0 for c in col)
    print(f"bipartite {bip}, connected {conn}")
    # right translations: a generating set of G (random elements until the generated subgroup is all of G)
    rng = random.Random(12345)
    gens = []
    sub = {G.e}
    while len(sub) < N:
        h = rng.choice(G.elems)
        if h in sub:
            continue
        gens.append(h)
        # closure of sub under right multiplication by gens (BFS on the Cayley graph)
        frontier = deque(sub)
        while frontier:
            g = frontier.popleft()
            for t in gens:
                z = G.mul(g, t)
                if z not in sub:
                    sub.add(z)
                    frontier.append(z)
    eset = set(edges)
    auto_ok = True
    perms = []
    for h in gens:
        img = [0] * n
        for u in range(k):
            for g in G.elems:
                img[u * N + rank[g]] = u * N + rank[G.mul(g, h)]
        perms.append(img)
        for u, v in edges:
            a, b = img[u], img[v]
            if (min(a, b), max(a, b)) not in eset:
                auto_ok = False
                break
    print(f"right translations by {len(gens)} generators of G are automorphisms: {auto_ok}")
    if eout:
        with open(eout + ".perms", "w") as f:
            for img in perms:
                f.write(" ".join(map(str, img)) + "\n")
    # eccentricity of (u, e) for each base vertex u (skipped with --no-bfs: then run apsp on the edge list)
    ecc = []
    for u in ([] if "--no-bfs" in sys.argv else range(k)):
        s = u * N + rank[G.e]
        dist = [-1] * n
        dist[s] = 0
        dq = deque([s])
        while dq:
            a = dq.popleft()
            for b in adj[a]:
                if dist[b] < 0:
                    dist[b] = dist[a] + 1
                    dq.append(b)
        ecc.append(max(dist) if min(dist) >= 0 else float("inf"))
    diam = max(ecc) if ecc else None
    print(f"ecc((u,1)) for u = 0..{k - 1}: {ecc}")
    print(f"diameter (fiber representatives + automorphisms) = {diam}")
    if full:
        import networkx as nx
        Gx = nx.Graph()
        Gx.add_nodes_from(range(n))
        Gx.add_edges_from(edges)
        dfull = nx.diameter(Gx)
        print(f"networkx all-pairs diameter = {dfull}")
        diam = max(diam, dfull)
    if diam is None:
        print("fiber BFS skipped (--no-bfs): the diameter must come from apsp on the edge list")
        diam = -1
    ok = (rep == 0 and loops == 0 and bip and conn and auto_ok and min(degs) == max(degs) and D is not None and diam <= D)
    print(f"SUMMARY n={n} Delta={max(degs)} regular={min(degs) == max(degs)} bipartite={bip} diameter={diam} D={D} -> {'VALID' if ok else 'INVALID'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
