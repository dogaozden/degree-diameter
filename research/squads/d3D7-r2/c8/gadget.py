# Start graph for sa3: GH(2) incidence graph plus `a` "+2 gadgets".
# Gadget: delete 3 disjoint edges (p_i, l_i); add a line-side hub u ~ p_1,p_2,p_3 and a point-side hub v ~ l_1,l_2,l_3.
# Result stays cubic and bipartite (n += 2). Output relabelled so sa3's convention holds: side A = 0..n/2-1.
import random, sys
gh = open(sys.argv[1]).read().split()
a = int(sys.argv[2]); seed = int(sys.argv[3]); out = sys.argv[4]
random.seed(seed)
n0 = int(gh[0]); E = [(int(gh[i]), int(gh[i+1])) for i in range(1, len(gh), 2)]
side = lambda v: 0 if v < n0 // 2 else 1     # GH: points 0..62 (A), lines 63..125 (B)
E = [(x, y) if side(x) == 0 else (y, x) for x, y in E]
# nodes: A-vertices as ('A', id), B-vertices as ('B', id); new ones appended
Ae = [('A', i) for i in range(n0 // 2)]; Be = [('B', i) for i in range(n0 // 2)]
edges = [(('A', x), ('B', y - n0 // 2)) for x, y in E]
for _ in range(a):
    picked = random.sample(range(len(edges)), 3)
    # ensure the three removed edges are pairwise vertex-disjoint
    while True:
        picked = random.sample(range(len(edges)), 3)
        As = {edges[i][0] for i in picked}; Bs = {edges[i][1] for i in picked}
        if len(As) == 3 and len(Bs) == 3: break
    removed = [edges[i] for i in picked]
    edges = [e for i, e in enumerate(edges) if i not in picked]
    u = ('B', len(Be)); Be.append(u)           # line-side hub on B
    v = ('A', len(Ae)); Ae.append(v)           # point-side hub on A
    for (pa, lb) in removed:
        edges.append((pa, u)); edges.append((v, lb))
n = len(Ae) + len(Be); m = n // 2
assert len(Ae) == m and len(Be) == m
idx = {x: i for i, x in enumerate(Ae)}; idx.update({x: m + i for i, x in enumerate(Be)})
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for x, y in edges: f.write(f"{idx[x]} {idx[y]}\n")
