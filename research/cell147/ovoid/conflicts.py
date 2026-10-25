import sys, numpy as np, collections
sys.path.insert(0, '.')
q = 11
P = np.load('/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/w/pts11.npy')
R = np.loadtxt(sys.argv[1], dtype=np.int64, comments='#') % q
inv = np.array([0] + [pow(i, q - 2, q) for i in range(1, q)])
first = np.argmax(R != 0, axis=1); R = R * inv[R[np.arange(len(R)), first]][:, None] % q
Y = R[:, [4, 5, 6, 3, 0, 1, 2]].copy(); Y[:, 3] = (-2 * Y[:, 3]) % q
c = np.zeros(len(P), dtype=np.int64)
for s in range(0, len(P), 20000):
    Bm = (P[s:s + 20000] @ Y.T) % q
    c[s:s + 20000] = (Bm == 0).sum(axis=1)
code = lambda X: (X * (q ** np.arange(7))).sum(axis=1)
inR = np.isin(code(P), code(R))
print('points in R:', inR.sum(), ' c on R (self only):', collections.Counter(c[inR].tolist()))
cnt = collections.Counter(c[~inR].tolist())
print('outside points by number of orthogonal R points (c: count):', sorted(cnt.items()))
np.save(sys.argv[2], c)
