# Builds the Omega-B1 construction of thesis section 2.9.3 for B1 = incidence graph of H(q), alpha given.
# Copies: 5*alpha copies of B1 (N1 = 2n vertices each). Hubs: 5*N1 'K1' vertices of degree 2*alpha.
# Every copy vertex receives exactly 2 hub neighbours (so every vertex has degree Delta1+2 = 2*alpha).
# Flip f_c per copy keeps the whole graph bipartite: global class = class(v) XOR f_c; a hub touches one global class only.
# Mode M1: all attachments of a hub at ONE base vertex t (the reading that the squad lead used).
# Mode M2: attachments of a hub at base vertices of BOTH classes (as the thesis figure 2.21 suggests), random design.
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex

def build(q, mode, seed, out):
    rnd = random.Random(seed)
    n, lines = load_hex(q)              # n points (class 0), n lines (class 1)
    N1 = 2 * n
    d1 = q + 1
    alpha = (d1 + 2) // 2               # Delta1 + 2 = 2*alpha (q=3 -> 6 -> alpha=3)
    assert 2 * alpha == d1 + 2
    C = 5 * alpha
    H = 5 * N1
    base = [(int(p), n + int(l)) for l in range(n) for p in lines[l]]
    flip = [0] * 6 + [1] * (C - 6) if alpha == 3 else [c % 2 for c in range(C)]
    F0 = [c for c in range(C) if flip[c] == 0]
    F1 = [c for c in range(C) if flip[c] == 1]
    def cls(v): return 0 if v < n else 1
    def gclass(c, v): return cls(v) ^ flip[c]
    edges = []
    for c in range(C):
        for a, b in base:
            edges.append((c * N1 + a, c * N1 + b))
    hub0 = C * N1
    hubs_t1 = H // 2                    # hubs attached to global class 0 copy vertices
    if mode == 'M1':
        # single base vertex per hub; needs |F0| = 6, |F1| = 9 (alpha=3, q=3 case)
        assert len(F0) == 6 and len(F1) == 9
        h = 0
        def add_hub(att):
            nonlocal h
            for (c, v) in att:
                edges.append((hub0 + h, c * N1 + v))
            h += 1
        g = [F1[0:3], F1[3:6], F1[6:9]]
        for t in range(N1):
            if cls(t) == 0:
                # type-1 hubs (global 0): copies with flip 0, 2 hubs cover each of the 6 copies twice
                for _ in range(2): add_hub([(c, t) for c in F0])
                # type-0 hubs (global 1): copies with flip 1, 3 hubs, complements of the 3 groups
                add_hub([(c, t) for c in g[1] + g[2]])
                add_hub([(c, t) for c in g[0] + g[2]])
                add_hub([(c, t) for c in g[0] + g[1]])
            else:
                for _ in range(3):
                    pass
                # type-1 hubs for t in class 1: copies with flip 1 (3 hubs as above)
                add_hub([(c, t) for c in g[1] + g[2]])
                add_hub([(c, t) for c in g[0] + g[2]])
                add_hub([(c, t) for c in g[0] + g[1]])
                # type-0 hubs for t in class 1: copies with flip 0 (2 hubs)
                for _ in range(2): add_hub([(c, t) for c in F0])
        assert h == H, (h, H)
    else:
        # M2: random design, each hub takes 2*alpha slots from distinct copies, vertices of both classes
        for target in (0, 1):
            # pools: per copy, list of vertices v with gclass(c,v)==target, each used twice
            pools = {c: [v for v in range(N1) if gclass(c, v) == target for _ in range(2)] for c in range(C)}
            for c in range(C): rnd.shuffle(pools[c])
            nh = hubs_t1
            mixed = 0
            for k in range(nh):
                rem = sorted(range(C), key=lambda c: (-len(pools[c]), rnd.random()))
                pick = rem[:2 * alpha]
                assert all(len(pools[c]) > 0 for c in pick)
                classes = set()
                for c in pick:
                    v = pools[c].pop()
                    classes.add(cls(v))
                    edges.append((hub0 + (hubs_t1 * target + k) if False else hub0 + (k if target == 0 else hubs_t1 + k), c * N1 + v))
                mixed += (len(classes) == 2)
            print('target', target, 'hubs', nh, 'mixed-class hubs', mixed, file=sys.stderr)
            assert all(len(pools[c]) == 0 for c in range(C))
    total = C * N1 + H
    with open(out, 'w') as f:
        f.write(f"{total}\n")
        f.write("\n".join(f"{a} {b}" for a, b in edges))
        f.write("\n")
    deg = [0] * total
    for a, b in edges:
        deg[a] += 1; deg[b] += 1
    print(mode, 'N=', total, 'edges=', len(edges), 'degrees', sorted(set(deg)), file=sys.stderr)

if __name__ == '__main__':
    q = int(sys.argv[1]); mode = sys.argv[2]; seed = int(sys.argv[3]); out = sys.argv[4]
    build(q, mode, seed, out)
