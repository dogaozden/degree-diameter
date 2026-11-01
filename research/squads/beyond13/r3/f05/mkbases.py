# Build 4-regular bipartite simple bases (girth >= 6) for liftd: format "nverts" then "u v" lines, sides [0,h),[h,2h).
import random, itertools, sys
def write(name, b, edges):
    with open(name, "w") as f:
        f.write(f"{b}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
def girth_ok(h, adj, minc=6):
    # adj: list of neighbour sets over 2h vertices; reject 4-cycles (no two A vertices share >= 2 nbrs)
    for a in range(h):
        for a2 in range(a+1, h):
            if len(adj[a] & adj[a2]) >= 2: return False
    return True
def random_base(h, seed):
    rnd = random.Random(seed)
    for attempt in range(10000):
        # random 4-regular bipartite via 4 random perfect matchings, reject multi-edges/4-cycles
        adjA = [set() for _ in range(h)]
        ok = True
        for k in range(4):
            perm = list(range(h)); rnd.shuffle(perm)
            for a in range(h):
                if perm[a] in adjA[a]: ok = False; break
            if not ok: break
            for a in range(h): adjA[a].add(perm[a])
        if ok and girth_ok(h, adjA):
            return [(a, h + b) for a in range(h) for b in adjA[a]]
    return None
def pg23_incidence():
    # projective plane of order 3: points/lines = 13 each; incidence graph degree 4, girth 6
    pts = []
    for v in itertools.product(range(3), repeat=3):
        if v == (0,0,0): continue
        # normalise: first nonzero coordinate = 1
        nz = [x for x in v if x][0]
        if nz == 1: pts.append(v)
    inc = []
    for i, L in enumerate(pts):
        for j, P in enumerate(pts):
            if sum(a*b for a, b in zip(L, P)) % 3 == 0: inc.append((j, 13 + i))
    return 26, inc
def gq33_incidence():
    # W(3): points of PG(3,3), lines = totally isotropic 2-spaces of symplectic form; incidence graph 40+40, degree 4, girth 8
    pts = []
    for v in itertools.product(range(3), repeat=4):
        if v == (0,0,0,0): continue
        nz = [x for x in v if x][0]
        if nz == 1: pts.append(v)
    def B(p, q): return (p[0]*q[1] - p[1]*q[0] + p[2]*q[3] - p[3]*q[2]) % 3
    idx = {p: i for i, p in enumerate(pts)}
    def norm(v):
        v = tuple(x % 3 for x in v); nz = [x for x in v if x][0]
        inv = 1 if nz == 1 else 2
        return tuple((x*inv) % 3 for x in v)
    lines = set()
    for p in pts:
        for q in pts:
            if p < q and B(p, q) == 0:
                span = set()
                for a in range(3):
                    for c in range(3):
                        if a == 0 and c == 0: continue
                        span.add(norm(tuple(a*x + c*y for x, y in zip(p, q))))
                lines.add(frozenset(span))
    lines = sorted(lines, key=lambda s: sorted(idx[x] for x in s))
    assert len(lines) == 40, len(lines)
    inc = []
    for i, L in enumerate(lines):
        for P in L: inc.append((idx[P], 40 + i))
    return 80, inc
if __name__ == "__main__":
    b, e = pg23_incidence(); write("base_pg23.txt", b, e); print("pg23", b, len(e))
    b, e = gq33_incidence(); write("base_gq33.txt", b, e); print("gq33", b, len(e))
    for h in (10, 13, 15, 20, 25, 30, 35, 40):
        for s in range(3):
            e = random_base(h, 1000*h + s)
            if e: write(f"base_rand{2*h}_{s}.txt", 2*h, e); print("rand", 2*h, s, len(e))
