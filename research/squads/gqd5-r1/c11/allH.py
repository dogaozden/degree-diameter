"""All-H level graphs over W(q): every matching = phi restricted to points, every freed set = elliptic quadric
(an ovoid of W(q)), B-hubs and A-hubs as in the brief, hub graph Y random (q-r)-regular bipartite until apsp is VALID.
usage: python3 allH.py q r [trials] [seed]"""
import sys, os, json, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib, levels
from duality import duality, OUT

q, r = int(sys.argv[1]), int(sys.argv[2])
trials = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
rng = random.Random(seed)

G, phi_pt, phi_line = duality(q)
F = G.F; q_ = q
# elliptic quadric Q-(3,q): x0x2 + x1^2 + x1x3 + a x3^2, polar form = w; ovoid of W(q)
a = next(a for a in range(q) if all(F.add[F.add[F.mul[x][x]][x]][a] != 0 for x in range(q)))
def Qf(v):
    s = F.add[F.mul[v[0]][v[2]]][F.mul[v[1]][v[1]]]
    s = F.add[s][F.mul[v[1]][v[3]]]
    return F.add[s][F.mul[a][F.mul[v[3]][v[3]]]]
O = [i for i, v in enumerate(G.coords) if Qf(v) == 0]
assert len(O) == q * q + 1 and gqlib.is_partial_ovoid(G, O)
assert all(len(set(L) & set(O)) == 1 for L in G.lines)
print('W(%d): ovoid of size %d verified (a=%d)' % (q, len(O), a), flush=True)

n_lev = 2 * r + 1
types = ['H'] * n_lev
trans = [(j, k) for j in range(n_lev) for k in range(1, r + 1)]
M = {t: list(phi_pt) for t in trans}
R = {t: set(O) for t in trans}
Bhubs = [[(j, x, (j, k)) for j in range(n_lev)] for x in O for k in range(1, r + 1)]
Ahubs = [[(j, phi_pt[x], ((j - k) % n_lev, k)) for j in range(n_lev)] for x in O for k in range(1, r + 1)]
K = len(Bhubs); dY = q - r
assert K == r * (q * q + 1) == len(Ahubs)
d = q + 1 + r
tmp = os.path.join(OUT, 'tmp_q%d_r%d.txt' % (q, r))
best = None
for tr in range(trials):
    Y = set()
    for _ in range(dY):
        perm = list(range(K)); rng.shuffle(perm)
        Y |= {(h, perm[h]) for h in range(K)}
    if len(Y) != K * dY:      # multi-edge: resample
        continue
    Y = sorted(Y)
    n, edges = levels.build(G, types, M, R, Bhubs, Ahubs, Y)
    levels.write_edges(tmp, n, edges)
    out = levels.apsp(tmp, d, 5)
    if tr == 0 or tr % 200 == 0:
        print('trial', tr, out, flush=True)
    if out.startswith('RESULT VALID'):
        best = (tr, n, edges, out)
        break
if best is None:
    print('NO VALID HUB GRAPH in %d trials; n=%d' % (trials, n))
    sys.exit(0)
tr, n, edges, out = best
final = os.path.join(OUT, 'edges_q%d_r%d.txt' % (q, r))
levels.write_edges(final, n, edges)
os.remove(tmp)
print('trial', tr, out, 'edges file', final, flush=True)
print(json.dumps({'q': q, 'r': r, 'n': n, 'd': d, 'D': 5, 'K': K, 'Y_degree': dY, 'seed': seed, 'trial': tr,
                  'result': out}))
