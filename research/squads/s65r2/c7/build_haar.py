# usage: python3 -I build_haar.py HXFILE "s0 s1 s2 s3 s4 s5" OUT.edges
# Haar graph H(G,S): vertices (g,0) = g, (g,1) = N+g, edges (g,0) ~ (s g,1) for s in S.
import sys
hx, S, out = sys.argv[1], [int(x) for x in sys.argv[2].split()], sys.argv[3]
tok = open(hx).read().split()
N = int(tok[0]); M = [int(x) for x in tok[1:1 + N * N]]
edges = set()
for g in range(N):
    for s in S:
        u = g; v = N + M[s * N + g]
        edges.add((min(u, v), max(u, v)))
with open(out, 'w') as f:
    f.write(f"{2 * N}\n")
    for u, v in sorted(edges):
        f.write(f"{u} {v}\n")
print("n", 2 * N, "edges", len(edges), "S", S)
