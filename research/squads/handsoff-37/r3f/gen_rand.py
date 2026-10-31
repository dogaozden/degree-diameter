# gen_rand.py M SEED OUT: random simple cubic bipartite graph on M+M vertices (A = 0..M-1, B = M..2M-1)
import random, sys
M, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rnd = random.Random(seed)
while True:
    edges = set()
    ok = True
    for _ in range(3):
        p = list(range(M)); rnd.shuffle(p)
        for a in range(M):
            e = (a, M + p[a])
            if e in edges: ok = False; break
            edges.add(e)
        if not ok: break
    if ok: break
with open(out, 'w') as f:
    f.write(f"{2*M}\n")
    for a, b in sorted(edges):
        f.write(f"{a} {b}\n")
