# Builds bipartite base graphs (edge lists, 0-based) for voltage lifts:
#   gq55  : incidence graph of W(5) = GQ(5,5) (312 vertices, 6-regular, diameter 4)
#   pg25  : incidence graph of PG(2,5)        (62 vertices, 6-regular, diameter 3)
#   pg27  : incidence graph of PG(2,7)        (114 vertices, 8-regular, diameter 3)
import itertools, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))

def norm(v, p):
    for x in v:
        if x % p:
            inv = pow(x, p - 2, p)
            return tuple((y * inv) % p for y in v)
    return None

def proj_points(dim, p):
    pts = set()
    for v in itertools.product(range(p), repeat=dim):
        n = norm(v, p)
        if n is not None:
            pts.add(n)
    return sorted(pts)

def write(name, N, edges):
    with open(os.path.join(HERE, name), 'w') as f:
        f.write(f"{N} {len(edges)}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")
    print(name, "N=", N, "E=", len(edges))

def pg2(p):
    P = proj_points(3, p)
    idx = {x: i for i, x in enumerate(P)}
    n = len(P)
    edges = []
    for i, x in enumerate(P):
        for j, l in enumerate(P):
            if sum(a * b for a, b in zip(x, l)) % p == 0:
                edges.append((i, n + j))
    return 2 * n, edges

def gq_w5():
    p = 5
    P = proj_points(4, p)
    n = len(P)
    def B(x, y):
        return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % p
    lines = set()
    for i in range(n):
        for j in range(i + 1, n):
            if B(P[i], P[j]) != 0:
                continue
            pts = set()
            for a, b in [(1, t) for t in range(p)] + [(0, 1)]:
                v = tuple((a*P[i][k] + b*P[j][k]) % p for k in range(4))
                nv = norm(v, p)
                pts.add(nv)
            lines.add(frozenset(P.index(q) for q in pts))
    lines = sorted(sorted(l) for l in lines)
    assert len(lines) == n, len(lines)
    edges = []
    for j, L in enumerate(lines):
        for i in L:
            edges.append((i, n + j))
    return 2 * n, edges

if __name__ == "__main__":
    N, E = gq_w5(); write("base_gq55.txt", N, E)
    N, E = pg2(5); write("base_pg25.txt", N, E)
    N, E = pg2(7); write("base_pg27.txt", N, E)
