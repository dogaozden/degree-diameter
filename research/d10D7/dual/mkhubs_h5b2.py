"""Hub layout for the 5-level (12,7) graph: the 2-level cover of H(5) with B2 hubs.
Levels A, B: hexagon edges in each, (p,A) ~ (M(p),B) and (p,B) ~ (M(p),A) for every non-freed point p (M, freed
points and their hub graph from the (7,7) solution d7D7_hex5_B2K72_n23580.sol, which satisfies the B2 condition).
A freed pair (p, l = M(p)) loses its two cover edges and gets z_p ~ (p,A),(p,B) and z'_l ~ (l,A),(l,B); the z's are
linked by the solution's hub graph (degree 4). Hub-graph degree <= 7 everywhere.
Line-side hubs: points of A (0..N-1), points of B (N..2N-1), z'_l (2N..2N+K5-1).
Point-side hubs: lines of A, lines of B, z_p.   Owners: freed point j % K of the big graph.
usage: python3 mkhubs_h5b2.py SOL5 K out_hubs out_hubgraph_edges"""
import struct, sys
sol5, K, out_hubs, out_edges = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
f = open('/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin', 'rb'); q, N, L = struct.unpack('3i', f.read(12))
LP = struct.unpack('%di' % (L * (q + 1)), f.read(4 * L * (q + 1)))
tok = open(sol5).read().split(); assert tok[0] == 'd7hex' and int(tok[1]) == q and int(tok[2]) == N
K5 = int(tok[3]); i = 5; assert tok[i] == 'freed'; i += 1
fp = [int(x) for x in tok[i:i + K5]]; i += K5
assert tok[i] == 'hubedges'; hm = int(tok[i + 1]); i += 2
he = [(int(tok[i + 2 * e]), int(tok[i + 2 * e + 1])) for e in range(hm)]; i += 2 * hm
M = [int(x) for x in tok[i:i + N]]; assert len(M) == N
fl = [M[p] for p in fp]; freed = set(fp)
edges = []
for c in range(2):
    edges += [(c * N + LP[l * (q + 1) + t], c * N + l) for l in range(L) for t in range(q + 1)]
for p in range(N):
    if p in freed: continue
    edges.append((p, N + M[p]))          # (p,A) ~ (M(p),B)
    edges.append((N + p, M[p]))          # (p,B) ~ (M(p),A)
for k, p in enumerate(fp):
    edges += [(p, 2 * N + k), (N + p, 2 * N + k)]                 # z_p (point-side 2N+k) ~ (p,A), (p,B)
for k, l in enumerate(fl):
    edges += [(2 * N + k, l), (2 * N + k, N + l)]                 # z'_l (line-side 2N+k) ~ (l,A), (l,B)
for a, b in he:                                                   # line-side hub a ~ point-side hub b of the (7,7) graph
    edges.append((2 * N + b, 2 * N + a))                          # here: z'_{l_b} (line-side) ~ z_{p_a} (point-side)
HL = HP = 2 * N + K5
assert len(set(edges)) == len(edges), 'repeated edge'
degL = [0] * HL; degP = [0] * HP
for j, k in edges: degL[j] += 1; degP[k] += 1
print('HL', HL, 'edges', len(edges), 'max degree', max(degL), max(degP), 'K5', K5, 'hub-graph edges', hm)
assert max(degL) <= 7 and max(degP) <= 7 and HL <= 2 * K
own = [j % K for j in range(HL)]
with open(out_hubs, 'w') as o:
    o.write('%d %d %d\n' % (HL, HP, len(edges))); o.write(' '.join(map(str, own)) + '\n'); o.write(' '.join(map(str, own)) + '\n')
    o.writelines('%d %d\n' % e for e in edges)
with open(out_edges, 'w') as o:                                   # hub graph alone: line-side j -> j, point-side k -> HL + k
    o.write('%d\n' % (HL + HP)); o.writelines('%d %d\n' % (j, HL + k) for j, k in edges)
