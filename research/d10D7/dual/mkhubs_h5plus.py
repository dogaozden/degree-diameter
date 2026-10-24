"""Hub layout for the 5-level (12,7) graph: the incidence graph of H(5) (3906 + 3906 hubs, degree 6, diameter 6) plus
X extra hubs per side, each attached to 7 hubs of the other side that still have a free slot (degree cap 7).
A new line-side hub reaches every old line-side hub within 1 + 5 = 6 through any attachment; two new hubs need two
attachments within distance 4 in H(5), which random choices give w.h.p. (checked afterwards with hubecc).
   python3 mkhubs_h5plus.py K X seed out_hubs out_hg"""
import struct, random, sys
K, X, seed, out_hubs, out_hg = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
f = open('/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin', 'rb'); q, N, L = struct.unpack('3i', f.read(12))
LP = struct.unpack('%di' % (L * (q + 1)), f.read(4 * L * (q + 1)))
rng = random.Random(seed)
permP = list(range(N)); rng.shuffle(permP); permL = list(range(L)); rng.shuffle(permL)
posP = {p: j for j, p in enumerate(permP)}; posL = {l: k for k, l in enumerate(permL)}
edges = [(posP[LP[l * (q + 1) + t]], posL[l]) for l in range(L) for t in range(q + 1)]
HL = HP = N + X
spareL = list(range(N)); spareP = list(range(N)); rng.shuffle(spareL); rng.shuffle(spareP)   # old hubs with 1 free slot each
for x in range(X):   # new line-side hub N + x attaches to 7 old point-side hubs; new point-side hub N + x to 7 old line-side hubs
    for _ in range(7): edges.append((N + x, spareP.pop()))
    for _ in range(7): edges.append((spareL.pop(), N + x))
ownL = [j % K for j in range(HL)]; ownP = [k % K for k in range(HP)]
assert max(ownL.count(i) for i in range(K)) <= 2
with open(out_hubs, 'w') as o:
    o.write('%d %d %d\n' % (HL, HP, len(edges))); o.write(' '.join(map(str, ownL)) + '\n'); o.write(' '.join(map(str, ownP)) + '\n')
    o.writelines('%d %d\n' % e for e in edges)
with open(out_hg, 'w') as o:
    o.write('%d %d\n' % (HL, len(edges))); o.writelines('%d %d\n' % e for e in edges)
print('HL', HL, 'edges', len(edges))
