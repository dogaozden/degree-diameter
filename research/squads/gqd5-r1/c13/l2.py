"""L = 2 levels of Q(5,2) joined by two line bijections sigma, tau (every line gets 2 matching edges, deg 5).
Usage: l2.py seed out.txt"""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
seed, out = int(sys.argv[1]), sys.argv[2]
G = gqlib.Q5(2); P, N = G.np, G.nl; per = P + N
rng = random.Random(seed)
edges = []
for j in range(2):
    b = j * per
    for l, pts in enumerate(G.lines):
        for p in pts:
            edges.append((b + p, b + P + l))
sig = list(range(N)); rng.shuffle(sig)
tau = list(range(N))
while True:
    rng.shuffle(tau)
    if all(sig[l] != tau[l] for l in range(N)): break
for l in range(N):
    edges.append((P + l, per + P + sig[l]))
    edges.append((P + l, per + P + tau[l]))
with open(out, 'w') as f:
    f.write('%d\n' % (2 * per))
    for a, b in edges: f.write('%d %d\n' % (a, b))
print(2 * per, len(edges))
