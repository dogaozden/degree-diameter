"""Corollary 10.1 at q = 8, r = 2 with an explicit duality of W(q), q even (Klein + projection from the nucleus):
psi(line <x,y>) = (p01, p03, p23, p12)."""
import sys, random, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, regular_spread_W, is_partial_ovoid, _norm
APSP = '/home/user/degree-diameter/research/theorems/d5gq/apsp'
q = int(sys.argv[1]); r = int(sys.argv[2]); K = int(sys.argv[3]); s_hub, r_hub = int(sys.argv[4]), int(sys.argv[5])
Wq = W(q); F = Wq.F; N = Wq.np
def pl(x, y, i, j): return F.sub[F.mul[x[i]][y[j]]][F.mul[x[j]][y[i]]]
psi = []
for l in Wq.lines:
    x, y = Wq.coords[l[0]], Wq.coords[l[1]]
    v = (pl(x, y, 0, 1), pl(x, y, 0, 3), pl(x, y, 2, 3), pl(x, y, 1, 2))
    psi.append(Wq.index[_norm(F, v)])
assert sorted(psi) == list(range(N)), 'psi not a bijection'
# psi maps concurrent lines to collinear points and conversely
con = Wq.con; col = Wq.col
P = np.array(psi)
assert np.array_equal(col[np.ix_(P, P)], con), 'psi not a duality on lines->points'
lid = {l: i for i, l in enumerate(Wq.lines)}
phi = []
for x in range(N):
    pts = tuple(sorted(psi[l] for l in Wq.plines[x]))
    phi.append(lid[pts])                      # the images of the lines through x form a line of W(q)
assert sorted(phi) == list(range(N))
O = [psi[l] for l in regular_spread_W(Wq)]
assert is_partial_ovoid(Wq, O) and len(O) == q * q + 1
print('explicit duality of W(%d) ok; ovoid psi(spread) ok' % q)
# level graph, all H, M = phi on every arc, R = O
L = 2 * r + 1; per = 2 * N
vid = lambda j, kind, i: j * per + (i if kind == 'P' else N + i)
edges = [(vid(j, 'P', p), vid(j, 'L', l)) for j in range(L) for l, pts in enumerate(Wq.lines) for p in pts]
Aslots = [[] for _ in range(L)]; Bslots = [[] for _ in range(L)]
Oset = set(O)
for j in range(L):
    for k in range(1, r + 1):
        j2 = (j + k) % L
        for p in range(N):
            u, v = vid(j, 'P', p), vid(j2, 'L', phi[p])
            if p in Oset: Aslots[j].append(u); Bslots[j2].append(v)
            else: edges.append((u, v))
nv = L * per
for h in range(K):
    for j in range(L): edges.append((nv + h, Aslots[j][h]))
for g in range(K):
    for j in range(L): edges.append((nv + K + g, Bslots[j][g]))
# hub graph (Y3): level graph over W(s_hub), 2 r_hub + 1 levels, all H, random bijections
Hs = W(s_hub); n_s = Hs.np; Lh = 2 * r_hub + 1; rng = random.Random(0)
assert Lh * n_s == K
Aid = lambda j, p: j * n_s + p          # A-element (point) -> A-hub index
Bid = lambda j, l: j * n_s + l          # B-element (line)  -> B-hub index
for j in range(Lh):
    for l, pts in enumerate(Hs.lines):
        for p in pts: edges.append((nv + Bid(j, l), nv + K + Aid(j, p)))
    for k in range(1, r_hub + 1):
        sig = list(range(n_s)); rng.shuffle(sig)
        for p in range(n_s): edges.append((nv + Bid((j + k) % Lh, sig[p]), nv + K + Aid(j, p)))
n = nv + 2 * K
path = 'even_q%d_r%d.edges' % (q, r)
with open(path, 'w') as f:
    f.write('%d\n' % n)
    for a, b in edges: f.write('%d %d\n' % (a, b))
print('n', n)
print(subprocess.run([APSP, path, str(q + 1 + r), '5'], capture_output=True, text=True).stdout.strip())
