# randbase.py BASE M SEED OUT: same base structure, tree edges (BFS from 0 in edge order, as tabu) voltage 0,
# all other voltages uniform random in 0..M-1 (parallel edges kept distinct). Used as random starts for vl / tabu.
import sys, random
base, M, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
with open(base) as f:
    toks = f.read().split('\n')
B, E = map(int, toks[0].split())
sides = toks[1]
edges = [tuple(map(int, l.split()[:2])) for l in toks[2:2 + E]]
adj = [[] for _ in range(B)]
for e, (u, w) in enumerate(edges):
    adj[u].append((w, e)); adj[w].append((u, e))
seen = [False] * B; seen[0] = True; q = [0]; tree = set(); qi = 0
while qi < len(q):
    x = q[qi]; qi += 1
    for y, e in adj[x]:
        if not seen[y]:
            seen[y] = True; q.append(y); tree.add(e)
volt = [0] * E
for e in range(E):
    if e in tree: continue
    u, w = edges[e]
    used = {volt[e2] for e2 in range(E) if edges[e2] == (u, w) and e2 < e}
    while True:
        v = rng.randrange(M)
        if v not in used: break
    volt[e] = v
with open(out, 'w') as f:
    f.write("%d %d\n%s\n" % (B, E, sides))
    for e, (u, w) in enumerate(edges): f.write("%d %d %d\n" % (u, w, volt[e]))
