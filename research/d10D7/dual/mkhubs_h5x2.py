"""Hub layout for the 5-level (12,7) graph: two copies A, B of the incidence graph of H(5) (degree 6, diameter 6) plus
two perfect matchings on the spare slot (degree 7): line-side(A) ~ point-side(B) and point-side(A) ~ line-side(B).
Every hub reaches every same-side hub of its own copy within 6, and of the other copy within 1 + 5 = 6 through its
spare edge. 7,812 hubs per side.   python3 mkhubs_h5x2.py K seed out_hubs out_hg"""
import struct, random, sys
K, seed, out_hubs, out_hg = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
f = open('/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin', 'rb'); q, N, L = struct.unpack('3i', f.read(12))
LP = struct.unpack('%di' % (L * (q + 1)), f.read(4 * L * (q + 1)))
rng = random.Random(seed); edges = []
for c in range(2):   # copy c: line-side hubs c*N + (point index), point-side hubs c*N + (line index), relabelled
    permP = list(range(N)); rng.shuffle(permP); permL = list(range(L)); rng.shuffle(permL)
    posP = {p: c * N + j for j, p in enumerate(permP)}; posL = {l: c * N + k for k, l in enumerate(permL)}
    edges += [(posP[LP[l * (q + 1) + t]], posL[l]) for l in range(L) for t in range(q + 1)]
m1 = list(range(N)); rng.shuffle(m1); m2 = list(range(N)); rng.shuffle(m2)
edges += [(j, N + m1[j]) for j in range(N)]          # line-side A j ~ point-side B
edges += [(N + j, m2[j]) for j in range(N)]          # line-side B j ~ point-side A
HL = HP = 2 * N
ownL = [j % K for j in range(HL)]; ownP = [k % K for k in range(HP)]
assert max(ownL.count(i) for i in range(min(K, 50))) <= 2 and HL <= 2 * K
with open(out_hubs, 'w') as o:
    o.write('%d %d %d\n' % (HL, HP, len(edges))); o.write(' '.join(map(str, ownL)) + '\n'); o.write(' '.join(map(str, ownP)) + '\n')
    o.writelines('%d %d\n' % e for e in edges)
with open(out_hg, 'w') as o:
    o.write('%d %d\n' % (HL, len(edges))); o.writelines('%d %d\n' % e for e in edges)
print('HL', HL, 'edges', len(edges))
