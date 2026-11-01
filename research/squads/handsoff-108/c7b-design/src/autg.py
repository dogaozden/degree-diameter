# autg.py (worker c7b): automorphism group generators of the incidence graph of H(q) via BLISS (python-igraph,
# installed under c7b-design/pylib). Writes autgens_q{q}.txt: one generator per line, as a permutation of the 2N
# vertices (points 0..N-1, lines N..2N-1), and prints the orbit counts on points and on flags.
import sys, os, struct, time
HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, os.path.join(HERE, 'pylib'))
import igraph as ig
q = int(sys.argv[1])
with open(os.path.join(HERE, 'hex', 'hex_q%d.bin' % q), 'rb') as f:
    qq, N, L = struct.unpack('<iii', f.read(12))
    pl = struct.unpack('<%di' % (L * (q + 1)), f.read(4 * L * (q + 1)))
edges = []
for l in range(N):
    for k in range(q + 1):
        edges.append((pl[l * (q + 1) + k], N + l))
g = ig.Graph(n=2 * N, edges=edges)
t0 = time.time()
gens = g.automorphism_group(sh='fl')
print('q=%d N=%d |generators|=%d time %.1fs' % (q, N, len(gens), time.time() - t0))
cnt = g.count_automorphisms(sh='fl')
print('group order (BLISS) = %d' % cnt)
with open(os.path.join(HERE, 'runs', 'autgens_q%d.txt' % q), 'w') as f:
    for pm in gens:
        f.write(' '.join(map(str, pm)) + '\n')
