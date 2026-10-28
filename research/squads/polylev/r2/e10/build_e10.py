"""Card e10: independent builder of the D = 11 lift from the director's q=3 colour files (no lift9.py).
usage: build_e10.py R SEED OUT_PREFIX
 1. balance: the 52 uncoloured points and 52 uncoloured lines get colours. A random set S of 52 colours
    receives one uncoloured point and one uncoloured line each, so every colour ends with |A_i| = |B_i|.
 2. sigma_t (t = 1..R): random bijection points -> lines mapping colour-i points onto colour-i lines.
 3. graph: m = 2RK+1, vertex (p,g) -> p*m+g, (l,g) -> (N+l)*m+g. Edges (p,g)-(l,g) for p on l;
    edges (z,g)-(sigma_t(z), g+(t-1)K+i+1 mod m) for z of colour i, t = 1..R.
Writes OUT_PREFIX.pcol, OUT_PREFIX.lcol (balanced colours), OUT_PREFIX.sigma.npy, OUT_PREFIX.edges.
"""
import sys, struct
import numpy as np

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q3.bin'
PCOL = '/home/user/degree-diameter/research/theorems/polylev/parts/qs_q3.pcol'
LCOL = '/home/user/degree-diameter/research/theorems/polylev/parts/qs_q3.lcol'
K = 78

R = int(sys.argv[1]); SEED = int(sys.argv[2]); OUT = sys.argv[3]
rng = np.random.default_rng(SEED)

with open(HEX, 'rb') as f:
    q, N, L = struct.unpack('<3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype='<i4').reshape(L, q + 1).astype(np.int64)
assert (q, N, L) == (3, 364, 364)

pc = np.fromfile(PCOL, dtype='<i4').astype(np.int64)
lc = np.fromfile(LCOL, dtype='<i4').astype(np.int64)
up = np.where(pc < 0)[0]; ul = np.where(lc < 0)[0]
assert len(up) == len(ul) == N - K * 4
S = rng.choice(K, size=len(up), replace=False)     # 52 distinct colours
rng.shuffle(up); rng.shuffle(ul)
pc[up] = S; lc[ul] = S
for i in range(K):
    assert (pc == i).sum() == (lc == i).sum() >= 4, i
np.asarray(pc, dtype='<i4').tofile(OUT + '.pcol')
np.asarray(lc, dtype='<i4').tofile(OUT + '.lcol')

m = 2 * R * K + 1
sig = []
for t in range(1, R + 1):
    s = np.full(N, -1, dtype=np.int64)
    for i in range(K):
        P = np.where(pc == i)[0]; Lb = np.where(lc == i)[0]
        s[P] = Lb[rng.permutation(len(Lb))]
    assert sorted(s.tolist()) == list(range(N))
    sig.append(s)
np.save(OUT + '.sigma.npy', np.array(sig))

G = np.arange(m, dtype=np.int64)
Us, Ws = [], []
# incidence edges, shift 0
Us.append((lines[:, :, None] * m + G[None, None, :]).ravel())
Ws.append(((N + np.arange(L))[:, None, None] * m + G[None, None, :] + 0 * lines[:, :, None]).ravel())
# sigma edges
z = np.arange(N)
for t in range(1, R + 1):
    lz = sig[t - 1]
    shift = (t - 1) * K + pc + 1                         # colour-dependent shift, per point z
    Us.append((z[:, None] * m + G[None, :]).ravel())
    Ws.append(((N + lz)[:, None] * m + (G[None, :] + shift[:, None]) % m).ravel())
U = np.concatenate(Us); W = np.concatenate(Ws)
n = 2 * N * m
assert U.min() >= 0 and W.min() >= 0 and U.max() < n and W.max() < n
assert (U != W).all()
E = np.stack([U, W], axis=1)
# sanity: simple, regular of degree 4 + R
key = np.minimum(U, W) * n + np.maximum(U, W)
assert len(np.unique(key)) == len(key), 'multi-edge'
deg = np.bincount(np.concatenate([U, W]), minlength=n)
print('n =', n, 'm =', m, 'edges =', len(E), 'degree min/max =', deg.min(), deg.max(), 'expected', 4 + R)
assert deg.min() == deg.max() == 4 + R
with open(OUT + '.edges', 'w') as f:
    f.write(f'{n}\n')
    np.savetxt(f, E, fmt='%d')
print('wrote', OUT + '.edges', 'colour counts per colour (points, lines):',
      [int((pc == i).sum()) for i in range(K)][:6], '...')
