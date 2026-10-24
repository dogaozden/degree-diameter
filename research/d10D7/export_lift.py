"""export_lift.py BASE SOL OUT : expand a lift2/dmfast solution (cyclic group Z_m, J matchings) over the polygon in
BASE (hex/ or gq/ bin file) into an explicit edge list for apsp.c: first line n, then "a b" per edge.
Lift vertex (x, h) -> x*m + h, x = 0..N-1 points, N..2N-1 lines; flag (p,l) with voltage g gives (p,h)~(l,h+g);
matching t gives (p,h)~(sigma_t(p), h + mv_t(p)).  Also prints n, edge count and the sha256 of the edge list."""
import struct, sys, hashlib
base, sol, out = sys.argv[1], sys.argv[2], sys.argv[3]
with open(base, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12)); Q1 = q + 1
    lines = [list(struct.unpack(f'{Q1}i', f.read(4 * Q1))) for _ in range(L)]
tok = open(sol).read().split('\n')
qq, J, m, D, cost = tok[0].split()[:5]; J, m = int(J), int(m)
spec = tok[1].split(); assert spec[0] == 'cyc' and int(spec[1]) == m, 'cyclic groups only'
rest = ' '.join(tok[2:]).split()
vals = list(map(int, rest))
sig = [vals[t * N:(t + 1) * N] for t in range(J)]
mv = [vals[J * N + t * N:J * N + (t + 1) * N] for t in range(J)]
hv = vals[2 * J * N:2 * J * N + N * Q1]
assert len(hv) == N * Q1
edges = []
for l, pts in enumerate(lines):
    for k, p in enumerate(pts):
        g = hv[l * Q1 + k]
        for h in range(m):
            edges.append((p * m + h, (N + l) * m + (h + g) % m))
for t in range(J):
    for p in range(N):
        for h in range(m):
            edges.append((p * m + h, (N + sig[t][p]) * m + (h + mv[t][p]) % m))
n = 2 * N * m
body = '\n'.join(f'{a} {b}' for a, b in edges) + '\n'
with open(out, 'w') as f:
    f.write(f'{n}\n'); f.write(body)
print('n', n, 'edges', len(edges), 'sha256(edge list file)', hashlib.sha256((f'{n}\n' + body).encode()).hexdigest())
