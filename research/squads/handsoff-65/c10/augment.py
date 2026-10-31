# augment.py IN OUT NAB SEED [PAIRS]: add j new vertex pairs to a voltage base (vl format).
# New pair(s): a (side 0) and b (side 1), n_ab parallel edges a-b, remove (6-n_ab) random base edges (u,v) and
# connect a to the freed side-1 ends and b to the freed side-0 ends. Voltages on new edges random in Z_m (m from argv).
import sys, random
inf, outf, nab, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
pairs = int(sys.argv[5]) if len(sys.argv) > 5 else 1
M = int(sys.argv[6]) if len(sys.argv) > 6 else 19
rnd = random.Random(seed)
L = open(inf).read().split('\n')
b0, E0 = map(int, L[0].split()[:2])
side = list(map(int, L[1].split()))
edges = []
for line in L[2:2+E0]:
    p = line.split()
    edges.append([int(p[0]), int(p[1]), int(p[2]) if len(p) > 2 else 0])
b = b0
for _ in range(pairs):
    a = b; bb = b + 1
    side += [0, 1]
    k = 6 - nab
    # pick k edges whose endpoints are not already touching a, bb (new vertices have none yet)
    idx = rnd.sample(range(len(edges)), k)
    removed = [edges[i] for i in idx]
    keep = [edges[i] for i in range(len(edges)) if i not in set(idx)]
    fu = [e[0] for e in removed]; fv = [e[1] for e in removed]
    rnd.shuffle(fv)
    rnd.shuffle(fu)
    edges = keep
    for v in fv:
        edges.append([a, v, rnd.randrange(M)])
    for u in fu:
        edges.append([u, bb, rnd.randrange(M)])
    for _ in range(nab):
        edges.append([a, bb, rnd.randrange(M)])
    b += 2
with open(outf, 'w') as f:
    f.write(f"{b} {len(edges)}\n")
    f.write(' '.join(map(str, side)) + '\n')
    for u, w, v in edges:
        f.write(f"{u} {w} {v}\n")
print("b", b, "E", len(edges))
