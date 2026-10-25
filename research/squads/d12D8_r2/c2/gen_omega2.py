# Omega-B1 test graphs for B1 = incidence graph of H(3) (alpha = 3, Delta = 6, 5*alpha = 15 copies).
# M1N (no flips, single base vertex per hub, cyclic design): for every base vertex t the 5 hubs at t are
#   attached to copies {3i,...,3i+5} mod 15 (i = 0..4), so each copy vertex (c,t) gets exactly 2 hubs.
# M2N: as M1N but each hub's 6 attachments at arbitrary base vertices of the SAME global class (no flips),
#   random design; this keeps every hub single-class and bipartite.
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex

def build(mode, seed, out, q=3):
    rnd = random.Random(seed)
    n, lines = load_hex(q)
    N1 = 2 * n; C = 15; H = 5 * N1
    base = [(int(p), n + int(l)) for l in range(n) for p in lines[l]]
    edges = []
    for c in range(C):
        for a, b in base:
            edges.append((c * N1 + a, c * N1 + b))
    hub0 = C * N1
    if mode == 'M1N':
        h = 0
        for t in range(N1):
            for i in range(5):
                for j in range(6):
                    c = (3 * i + j) % 15
                    edges.append((hub0 + h, c * N1 + t))
                h += 1
    elif mode == 'M2N':
        # each copy vertex (c,t) needs 2 hub slots; hubs of class-0 base vertices attach to class-0 base vertices
        for side in (0, 1):
            bases = [t for t in range(N1) if (0 if t < n else 1) == side]
            slots = [(c, t) for c in range(C) for t in bases for _ in range(2)]
            rnd.shuffle(slots)
            # 5 hubs per base vertex, 6 slots each: greedy with distinct copies per hub
            hubs_needed = 5 * len(bases)
            pools = {c: [] for c in range(C)}
            for (c, t) in slots: pools[c].append(t)
            hub_id = 0 if side == 0 else len(bases) * 5
            # hubs are numbered arbitrarily; attachments picked from copies with largest remaining pools
            k = 0
            for hi in range(hubs_needed):
                pick = sorted(range(C), key=lambda c: (-len(pools[c]), rnd.random()))[:6]
                for c in pick:
                    t = pools[c].pop()
                    edges.append((hub0 + (side * (5 * (N1 // 2)) + hi), c * N1 + t))
            assert all(len(pools[c]) == 0 for c in range(C))
    total = C * N1 + H
    with open(out, 'w') as f:
        f.write(f"{total}\n" + "\n".join(f"{a} {b}" for a, b in edges) + "\n")
    deg = [0] * total
    for a, b in edges: deg[a] += 1; deg[b] += 1
    print(mode, seed, 'N', total, 'edges', len(edges), 'degrees', sorted(set(deg)), file=sys.stderr)

if __name__ == '__main__':
    build(sys.argv[1], int(sys.argv[2]), sys.argv[3])
