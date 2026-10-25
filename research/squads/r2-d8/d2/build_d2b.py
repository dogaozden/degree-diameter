"""Variant B of card d2: each in-arc attaches to ONE copy of its head (the two in-arcs of h take copies 0 and 1),
so no K_{2,4} forms (variant A, the card's example, has in-arc pairs sharing all 4 of their other neighbours).
Layer: copies (v,i)~(x,i) for x adjacent to v in I (4), plus a random perfect matching between point-copies and
line-copies (1). Degrees: arc 4 (undirected line digraph) + 1 = 5; copy 1 (in-arc) + 4 + 1 = 6.
Usage: python3 build_d2b.py OUT [seed] [matching: rand|none]"""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d8/d2')
import build_d2 as B
import gh

def build_B(seed=1, matching=True):
    H = gh.load(3)
    arcs, N = B.eulerian_orientation(H, seed)
    nA = len(arcs)
    NC = 2 * (2 * N)
    NW = NC + nA
    in_at = [[] for _ in range(2 * N)]; out_at = [[] for _ in range(2 * N)]
    for k, (t, h) in enumerate(arcs):
        out_at[t].append(NC + k); in_at[h].append(NC + k)
    E = []
    for hv in range(2 * N):
        for idx, a in enumerate(in_at[hv]):
            E.append((a, 2 * hv + idx, 'ac'))
        for a in in_at[hv]:
            for b in out_at[hv]:
                E.append((a, b, 'aa'))
    flags = gh.flags(H)
    nbrs = [[] for _ in range(2 * N)]
    for u, w in flags:
        nbrs[u].append(w); nbrs[w].append(u)
    existing = set()
    for v in range(2 * N):
        for x in nbrs[v]:
            if v < x:
                for i in (0, 1):
                    E.append((2 * v + i, 2 * x + i, 'cc')); existing.add((2 * v + i, 2 * x + i))
    if matching:
        rng = random.Random(seed + 1000)
        P = list(range(N)); L = list(range(N, 2 * N))
        for _ in range(10000):
            Lc = [2 * l + i for l in L for i in (0, 1)]
            rng.shuffle(Lc)
            Pc = [2 * p + i for p in P for i in (0, 1)]
            pairs = list(zip(Pc, Lc))
            if all((a, b) not in existing and (b, a) not in existing for a, b in pairs):
                break
        for a, b in pairs:
            E.append((a, b, 'mt'))
    return NW, E, arcs, H

if __name__ == '__main__':
    out = sys.argv[1]; seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    matching = (sys.argv[3] if len(sys.argv) > 3 else 'rand') != 'none'
    NW, E, arcs, H = build_B(seed, matching)
    deg = [0] * NW
    for u, v, _ in E: deg[u] += 1; deg[v] += 1
    print('NW', NW, 'edges', len(E), 'deg range', min(deg), max(deg))
    rng = random.Random(seed)
    volts = [rng.randrange(5) for _ in E]
    B.write_lift_file(out, NW, E, volts)
