"""Independent builder for the (3,11) graph on 1,320 vertices: python3 -I build_d3D11_n1320.py SOL.txt OUT.edges
Voltages in C3 x (Z11 x|_3 Z5) coordinates (z, a, j); no GAP numbering used."""
import sys, itertools
base = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
base = [(t[0], t[1], tuple(t[2:5])) for t in base]
G = list(itertools.product(range(3), range(11), range(5)))
idx = {g: i for i, g in enumerate(G)}
def mul(g, h): return ((g[0] + h[0]) % 3, (pow(3, h[2], 11) * g[1] + h[1]) % 11, (g[2] + h[2]) % 5)
N = len(G); k = 1 + max(max(u, v) for u, v, _ in base)
E = sorted({tuple(sorted((u * N + idx[g], v * N + idx[mul(g, s)]))) for u, v, s in base for g in G})
open(sys.argv[2], 'w').write(f"{k * N}\n" + ''.join(f"{x} {y}\n" for x, y in E))
print(k * N, "vertices", len(E), "edges")
