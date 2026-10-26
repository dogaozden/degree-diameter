"""Line-only layout over Q(5,2): L copies of the incidence graph (27 points deg 5, 45 lines deg 3); points carry no
matching edges; lines carry one edge to the next level and one from the previous level (cycle of L levels).
Usage: cyc.py L seed out.txt"""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
L, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
G = gqlib.Q5(2)
P, N = G.np, G.nl
per = P + N
rng = random.Random(seed)
edges = []
for j in range(L):
    b = j * per
    for l, pts in enumerate(G.lines):
        for p in pts:
            edges.append((b + p, b + P + l))
for j in range(L):
    j2 = (j + 1) % L
    perm = list(range(N)); rng.shuffle(perm)
    for l in range(N):
        edges.append((j * per + P + l, j2 * per + P + perm[l]))
n = L * per
with open(out, 'w') as f:
    f.write('%d\n' % n)
    for a, b in edges:
        f.write('%d %d\n' % (a, b))
print(n, len(edges))
