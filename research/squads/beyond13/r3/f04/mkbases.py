import itertools, random, sys
OUT = "/home/user/degree-diameter/research/squads/beyond13/r3/f04/bases/"

def write(name, b, edges):
    h = b // 2
    # edges given as (u,v) with u in A=[0,h), v in B=[h,b)
    deg = [0]*b
    for u, v in edges:
        assert u < h <= v, (u, v)
        deg[u] += 1; deg[v] += 1
    assert all(d == 4 for d in deg), (name, deg)
    assert len(set(edges)) == len(edges)
    with open(OUT + name, "w") as f:
        f.write(f"{b}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")
    print(name, b, len(edges))

# 1. PG(2,3) incidence graph, 13+13 vertices, girth 6
def pg23():
    pts = []
    for v in itertools.product(range(3), repeat=3):
        if v == (0, 0, 0): continue
        # normalize: first nonzero = 1
        f = next(x for x in v if x)
        if f == 1: pts.append(v)
    assert len(pts) == 13
    E = [(i, 13 + j) for i, p in enumerate(pts) for j, l in enumerate(pts)
         if sum(a*b for a, b in zip(p, l)) % 3 == 0]
    write("pg23.txt", 26, E)

# 2. K5,5 minus perfect matching (bipartite double of K5)
def k55m():
    E = [(i, 5 + j) for i in range(5) for j in range(5) if i != j]
    write("k55m.txt", 10, E)

# 3. GQ(3,3)=W(3) incidence: points of PG(3,3), lines totally isotropic for symplectic form
def w33():
    pts = []
    for v in itertools.product(range(3), repeat=4):
        if v == (0, 0, 0, 0): continue
        f = next(x for x in v if x)
        if f == 1: pts.append(v)
    assert len(pts) == 40
    def B(p, q):
        return (p[0]*q[1] - p[1]*q[0] + p[2]*q[3] - p[3]*q[2]) % 3
    lines = set()
    for i, p in enumerate(pts):
        for j, q in enumerate(pts):
            if i < j and B(p, q) == 0:
                # span of p,q: all points a p + b q
                S = set()
                for a, b in itertools.product(range(3), repeat=2):
                    if (a, b) == (0, 0): continue
                    w = tuple((a*x + b*y) % 3 for x, y in zip(p, q))
                    f = next(x for x in w if x)
                    if f == 1: S.add(pts.index(w))
                lines.add(frozenset(S))
    lines = sorted(sorted(l) for l in lines)
    assert len(lines) == 40 and all(len(l) == 4 for l in lines), (len(lines))
    E = [(pi, 40 + j) for j, l in enumerate(lines) for pi in l]
    write("gq33.txt", 80, E)

# 4. random 4-regular bipartite graphs, girth >= 6 (no 4-cycles), h per side
def rnd4(h, seed, name):
    rng = random.Random(seed)
    for attempt in range(100000):
        # union of 4 random perfect matchings between A and B, reject 4-cycles (double edges too)
        M = [set() for _ in range(4)]
        ok = True
        E = set()
        for k in range(4):
            perm = list(range(h)); rng.shuffle(perm)
            for a in range(h):
                e = (a, h + perm[a])
                if e in E: ok = False; break
                E.add(e)
            if not ok: break
        if not ok: continue
        # check no 4-cycle: two A vertices share at most one neighbor
        nb = {a: set() for a in range(h)}
        for a, bb in E: nb[a].add(bb)
        for a1 in range(h):
            for a2 in range(a1+1, h):
                if len(nb[a1] & nb[a2]) > 1: ok = False; break
            if not ok: break
        if ok:
            write(name, 2*h, sorted(E)); return
    print("failed", name)

if __name__ == "__main__":
    pg23(); k55m(); w33()
    for h, s in [(10, 1), (15, 2), (20, 3), (30, 4)]:
        rnd4(h, s, f"g6r4_{2*h}.txt")
