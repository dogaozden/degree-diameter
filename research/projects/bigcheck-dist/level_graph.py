# Test generator for apsp_shard's "L,B" layout: L levels of B vertices, vertex (l, p) = l*B + p, and edges
# (l, p) ~ (l+1 mod L, p+s mod B) for every offset s in OFFSETS. The level shift v -> (v + B) mod LB maps each such edge
# to an edge of the same kind, so it is an automorphism. The graph is bipartite exactly when L is even, and simple
# when L >= 4 and the offsets are distinct mod B. Writes "n" then "u v" lines, as apsp.c reads them.
# Usage: python3 level_graph.py L B OFFSETS(comma list) OUT
import sys
L, B = int(sys.argv[1]), int(sys.argv[2])
offsets = [int(x) for x in sys.argv[3].split(',')]
E = []
for l in range(L):
    for p in range(B):
        for s in offsets:
            E.append((l * B + p, ((l + 1) % L) * B + (p + s) % B))
with open(sys.argv[4], 'w') as f:
    f.write(f'{L * B}\n')
    f.writelines(f'{u} {v}\n' for u, v in E)
print(sys.argv[4], L * B, len(E))
