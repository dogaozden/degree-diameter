"""Builder for a regular voltage lift over the cyclic group Z_N: python3 -I build_cyclic_lift.py SOL.txt N OUT.edges
SOL.txt: lines "u v s" (comments '#'); vertex (u, x) = u*N + x; edge (u, x) ~ (v, x + s mod N)."""
import sys
base = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
N = int(sys.argv[2]); k = 1 + max(max(u, v) for u, v, _ in base)
E = sorted({tuple(sorted((u * N + x, v * N + (x + s) % N))) for u, v, s in base for x in range(N)})
open(sys.argv[3], 'w').write(f"{k * N}\n" + ''.join(f"{a} {b}\n" for a, b in E))
print(k * N, "vertices", len(E), "edges")
