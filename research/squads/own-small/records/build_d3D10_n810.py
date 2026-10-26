"""Independent builder for the (3,10) graph on 810 vertices: python3 -I build_d3D10_n810.py SOL.txt OUT.edges
Reads the base edges with voltages in C3 x He3 coordinates and writes "n" then "x y" lines. No GAP numbering used."""
import sys, itertools
lines = [l.split() for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
base = [(int(t[0]), int(t[1]), tuple(int(x) for x in t[2:6])) for t in lines]
G = list(itertools.product(range(3), repeat=4))          # (z, a, b, c)
idx = {g: i for i, g in enumerate(G)}
def mul(g, h):
    return ((g[0] + h[0]) % 3, (g[1] + h[1]) % 3, (g[2] + h[2]) % 3, (g[3] + h[3] + g[1] * h[2]) % 3)
N = len(G); k = 1 + max(max(u, v) for u, v, _ in base)
E = sorted({tuple(sorted((u * N + idx[g], v * N + idx[mul(g, s)]))) for u, v, s in base for g in G})
open(sys.argv[2], 'w').write(f"{k * N}\n" + ''.join(f"{x} {y}\n" for x, y in E))
print(k * N, "vertices", len(E), "edges")
