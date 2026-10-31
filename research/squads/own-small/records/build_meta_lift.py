"""Builder for a regular voltage lift over a metacyclic group Z_m x| Z_k: python3 -I build_meta_lift.py SOL.txt m k s OUT.edges
Element (i, j) = a^i b^j, product (i,j)(i',j') = (i + s^j i' mod m, j + j' mod k). SOL.txt lines "u v i j";
vertex (u, g) = u*m*k + (i*k + j); edge (u, g) ~ (v, g*x)."""
import sys
base = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
m, k, s = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); N = m * k
idx = lambda g: g[0] * k + g[1]
mul = lambda g, h: ((g[0] + pow(s, g[1], m) * h[0]) % m, (g[1] + h[1]) % k)
G = [(i, j) for i in range(m) for j in range(k)]
nb = 1 + max(max(t[0], t[1]) for t in base)
E = sorted({tuple(sorted((u * N + idx(g), v * N + idx(mul(g, (x0, x1)))))) for (u, v, x0, x1) in base for g in G})
open(sys.argv[5], 'w').write(f"{nb * N}\n" + ''.join(f"{x} {y}\n" for x, y in E))
print(nb * N, "vertices", len(E), "edges")
