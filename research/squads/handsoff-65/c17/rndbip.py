import random, sys
# random 6-regular simple bipartite graph on 2*n_side vertices (6 disjoint random perfect matchings)
n_side = int(sys.argv[1]); seed = int(sys.argv[2]); out = sys.argv[3]
random.seed(seed)
adj = [set() for _ in range(n_side)]
for _ in range(6):
    while True:
        p = list(range(n_side)); random.shuffle(p)
        if all(p[a] not in adj[a] for a in range(n_side)): break
    for a in range(n_side): adj[a].add(p[a])
with open(out, 'w') as f:
    f.write("%d\n" % (2 * n_side))
    for a in range(n_side):
        for b in sorted(adj[a]): f.write("%d %d\n" % (a, n_side + b))
