"""Line-only layouts over Q(5,2) with an arbitrary bipartite level graph: L copies of the incidence graph
(27 points deg 5 carry no matching edges; 45 lines deg 3 carry at most 2 matching edges). Each level-graph edge
(j,j') gets a random partial matching between lines of j and lines of j' (greedy, degree cap 2).
Usage: levelgraph.py graph seed out.txt   graph in {K23, C4, C6, P5}"""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
name, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
LG = {'K23': (5, [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4)]),
      'C4': (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
      'C6': (6, [(i, (i + 1) % 6) for i in range(6)]),
      'P5': (5, [(0, 1), (1, 2), (2, 3), (3, 4)])}
L, E = LG[name]
G = gqlib.Q5(2); P, N = G.np, G.nl; per = P + N
rng = random.Random(seed)
edges = []
for j in range(L):
    b = j * per
    for l, pts in enumerate(G.lines):
        for p in pts:
            edges.append((b + p, b + P + l))
deg = {}
pairs = set()
for (j, k) in E:
    order = list(range(N)); rng.shuffle(order)
    for l in order:
        cand = list(range(N)); rng.shuffle(cand)
        for m in cand:
            u = j * per + P + l; v = k * per + P + m
            if (u, v) in pairs: continue
            if deg.get(u, 0) < 2 and deg.get(v, 0) < 2:
                pairs.add((u, v)); deg[u] = deg.get(u, 0) + 1; deg[v] = deg.get(v, 0) + 1
                edges.append((u, v)); break
n = L * per
with open(out, 'w') as f:
    f.write('%d\n' % n)
    for a, b in edges: f.write('%d %d\n' % (a, b))
print(name, n, len(edges))
