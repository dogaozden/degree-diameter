"""k = 2t+1 copies of a generalized n-gon's incidence graph, linked by t bijections points -> lines (table-audit).

Base: the incidence graph of a generalized quadrangle (W(q), n = 4) or hexagon (H(q), n = 6) from moore_build,
points 0..N-1, lines N..2N-1, (q+1)-regular, diameter n, point-line distances <= n-1.
Graph X_t: vertices (v, i), v in the base, i in Z_k, k = 2t+1; base edges inside every level; for j = 1..t the
bijection M_j(p) = N + (p + j*s) mod N gives edges (p, i) ~ (M_j(p), i + j).  Bipartite (points | lines),
(q+1+t)-regular, order k*2N.
Diameter <= n+1 for ANY bijections M_j (proof as research/squads/exp2/hexd7/README.md Lemma, with level offsets
+-j through M_j): from a point (p,0), level +j is reached by (p,0) -> (M_j(p), j) then a base path (<= 1+n);
level -j: a point x by a base path (p,0) ~> (M_j(x),0) (<= n-1) then (M_j(x),0) -> (x,-j), a line through such an x
in one more step (<= n+1); symmetrically from a line.  This is the k-copies reading of the table's D = 5 (GQ) and
D = 7 (hexagon) values credited to Delorme, Gomez and Quisquater.
Layout: vertex (v, i) = i*2N + v, so v -> v + 2N (mod k*2N) is an automorphism (apsp_orb.c, L = k, B = 2N).
Usage: xt_build.py BASE_EDGES t OUT [s]"""
import sys

base, t, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
s = int(sys.argv[4]) if len(sys.argv) > 4 else 7919
with open(base) as f:
    n = int(f.readline())
    E = [tuple(map(int, line.split())) for line in f if line.strip()]
N = n // 2
k = 2 * t + 1
B = 2 * N
with open(out, 'w') as f:
    f.write(f'{k * B}\n')
    for i in range(k):
        o = i * B
        f.writelines(f'{u + o} {v + o}\n' for u, v in E)
    for j in range(1, t + 1):
        for i in range(k):
            o, o2 = i * B, ((i + j) % k) * B
            f.writelines(f'{p + o} {N + (p + j * s) % N + o2}\n' for p in range(N))
print(out, 'k =', k, 'levels of', B, '->', k * B, 'vertices,', k * len(E) + t * k * N, 'edges')
