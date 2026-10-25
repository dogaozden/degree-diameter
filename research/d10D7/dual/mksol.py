"""Write a d7hex solution: X(M) with M = a duality phi (points -> lines), freed flags = its absolute flags, hub graph file.
   python3 mksol.py q N PHI ABS HUBGRAPH OUT.sol"""
import sys, struct
q, N = int(sys.argv[1]), int(sys.argv[2])
phi = struct.unpack('%di' % (2 * N), open(sys.argv[3], 'rb').read())
M = [phi[p] - N for p in range(N)]
assert sorted(M) == list(range(N))
flags = [tuple(map(int, l.split())) for l in open(sys.argv[4]) if l.strip()]
for p, l in flags: assert M[p] == l
hg = open(sys.argv[5]).read().split(); K = int(hg[0]); m = int(hg[1]); E = [(int(hg[2 + 2 * i]), int(hg[3 + 2 * i])) for i in range(m)]
assert K == len(flags), (K, len(flags))
with open(sys.argv[6], 'w') as f:
    f.write('d7hex %d %d %d %d\nfreed %s\n' % (q, N, K, 6 * N + 2 * K, ' '.join(str(p) for p, l in flags)))
    f.write('hubedges %d %s\n' % (m, ' '.join('%d %d' % e for e in E)))
    for i in range(0, N, 20): f.write(' '.join(str(x) for x in M[i:i + 20]) + '\n')
print('K', K, 'n', 6 * N + 2 * K)
