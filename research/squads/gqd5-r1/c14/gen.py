"""gen.py SOL BASEBIN OUT MODE ARGS...
Doubled-matching lift (dmfast OUT format, Z6, q=4 base gq/gq_q4.bin) plus hub surgery.
Lift vertex (x,h) -> 6x+h; points x < Np, lines Np+l.
MODE star  : S = points given as comma list or 'all'; for each p in S delete its 12 matching edges and attach
             nL line-hubs to the six copies of p (one slot each) and nP point-hubs to the six copies of sigma(p).
Writes edge file "n" + "u v" lines.  Prints n and the number of hubs."""
import struct, sys
sol, base, out, mode = sys.argv[1:5]
args = sys.argv[5:]
with open(base, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12)); Q1 = q + 1
    lines = [list(struct.unpack(f'{Q1}i', f.read(4 * Q1))) for _ in range(L)]
tok = open(sol).read().split('\n')
qq, J, m, D, cost = tok[0].split()[:5]; J, m = int(J), int(m)
vals = list(map(int, ' '.join(tok[2:]).split()))
sig = [vals[t * N:(t + 1) * N] for t in range(J)]
mv = [vals[J * N + t * N:J * N + (t + 1) * N] for t in range(J)]
hv = vals[2 * J * N:2 * J * N + N * Q1]
flags = []
for l, pts in enumerate(lines):
    for k, p in enumerate(pts):
        flags.append((p * m, (N + l) * m, hv[l * Q1 + k]))
mat = []   # (p, t) matching edges
for t in range(J):
    for p in range(N):
        mat.append((p, t, sig[t][p], mv[t][p]))
def mat_edges_at(p):
    return [(p, t, s, v) for (pp, t, s, v) in mat if pp == p]
if mode == 'star':
    S = list(range(N)) if args[0] == 'all' else [int(x) for x in args[0].split(',')]
    nL, nP = int(args[1]), int(args[2])
    dele = set()
    for p in S:
        for (pp, t, s, v) in mat_edges_at(p):
            dele.add((pp, t))
    edges = []
    for (pp, t, s, v) in mat:
        if (pp, t) in dele: continue
        for h in range(m):
            edges.append((pp * m + h, (N + s) * m + (h + v) % m))
    for (pp, g) in []: pass
    for l, pts in enumerate(lines):
        for k, p in enumerate(pts):
            g = hv[l * Q1 + k]
            for h in range(m):
                edges.append((p * m + h, (N + l) * m + (h + g) % m))
    n = 2 * N * m
    hubs = 0
    for p in S:
        sp = [s for (pp, t, s, v) in mat if pp == p]
        for j in range(nL):
            for h in range(m):
                edges.append((n + hubs, p * m + h))
            hubs += 1
        for j in range(nP):
            for h in range(m):
                edges.append((n + hubs, (N + sp[0]) * m + h))
            hubs += 1
    ntot = n + hubs
else:
    raise SystemExit('unknown mode')
with open(out, 'w') as f:
    f.write(f'{ntot}\n' + ''.join(f'{a} {b}\n' for a, b in edges))
print('n', ntot, 'hubs', hubs, 'edges', len(edges))
