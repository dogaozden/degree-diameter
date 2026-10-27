"""exact max-weight clique in the compatibility graph of graphs/NAME.bin (tlimit seconds). usage: exact.py NAME TL"""
import sys, numpy as np, time
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from mwc import max_weight_clique
D = '/home/user/degree-diameter/research/squads/hexfam_r2/c3'
name, tl = sys.argv[1], float(sys.argv[2])
raw = np.fromfile('%s/graphs/%s.bin' % (D, name), dtype='<i4', count=2)
n, m = int(raw[0]), int(raw[1])
w = np.fromfile('%s/graphs/%s.bin' % (D, name), dtype='<i8', count=n, offset=8).tolist()
e = np.fromfile('%s/graphs/%s.bin' % (D, name), dtype='<i4', count=2 * m, offset=8 + 8 * n).reshape(m, 2)
conf = [[False] * n for _ in range(n)]
for a, b in e: conf[a][b] = conf[b][a] = True
adj = [0] * n
for i in range(n):
    bits = 0
    for j in range(n):
        if j != i and not conf[i][j]: bits |= 1 << j
    adj[i] = bits
t0 = time.time()
wgt, verts, done = max_weight_clique(w, adj, tl)
print(name, 'n', n, 'best', wgt, 'exact' if done else 'TIMELIMIT', 'orbits', len(verts), 'secs', round(time.time() - t0, 1), flush=True)
z = np.load('%s/graphs/%s.npz' % (D, name)); S, sizes, order, starts = z['S'], z['sizes'], z['order'], z['starts']
pts = np.sort(np.concatenate([order[starts[i]:starts[i] + sizes[i]] for i in verts]))
np.savetxt('%s/sets/%s_exact_%d.txt' % (D, name, len(pts)), pts, fmt='%d')
