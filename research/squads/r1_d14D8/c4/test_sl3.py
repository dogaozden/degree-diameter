"""Which block SL(3) (g on coordinate set W, g^{-T} on its partners) preserves the lines of H(11)?"""
import sys, itertools, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load
q = int(sys.argv[1]) if len(sys.argv) > 1 else 11
N, LP, PL, coord = load(q)
X = coord.astype(np.int64)
inv = np.zeros(q, dtype=np.int64)
for a in range(1, q): inv[a] = pow(a, q - 2, q)
pw = q ** np.arange(6, -1, -1, dtype=np.int64)
keys = X @ pw; order = np.argsort(keys); skeys = keys[order]
def normalize(Z):
    f = (Z != 0).argmax(axis=1); ld = Z[np.arange(len(Z)), f]
    return (Z * inv[ld][:, None]) % q
def pid_of(Y):
    k = Y @ pw; pos = np.searchsorted(skeys, k)
    ok = (skeys[np.clip(pos, 0, N-1)] == k)
    return np.where(ok, order[np.clip(pos, 0, N-1)], -1)
A0 = LP[:, 0]; A1 = LP[:, 1]
pk = np.minimum(A0, A1) * N + np.maximum(A0, A1); po = np.argsort(pk); spk = pk[po]
def line_of_pair(a, b):
    k = np.minimum(a, b) * N + np.maximum(a, b)
    pos = np.clip(np.searchsorted(spk, k), 0, len(spk) - 1)
    return np.where(spk[pos] == k, po[pos], -1)
def matinv(A):
    det = int(round(np.linalg.det(A))) % q; di = pow(det, q - 2, q)
    adj = np.zeros((3, 3), dtype=np.int64)
    for r in range(3):
        for s in range(3):
            minor = np.delete(np.delete(A, s, axis=0), r, axis=1)
            adj[r, s] = ((-1) ** (r + s)) * (minor[0, 0] * minor[1, 1] - minor[0, 1] * minor[1, 0])
    return (adj * di) % q
def block_act(g, Wc, Wd):
    ginv = matinv(g)
    Y = X.copy()
    Y[:, Wc] = (X[:, Wc] @ g.T) % q
    Y[:, Wd] = (X[:, Wd] @ ginv) % q
    return Y
def test(Y):
    Z = normalize(Y)
    gp = pid_of(Z)
    if (gp < 0).any(): return 'not-on-quadric'
    if len(np.unique(gp)) != N: return 'not-bijective'
    gl = line_of_pair(gp[A0], gp[A1])
    if (gl < 0).any(): return 'pair-not-on-line'
    ok = (np.sort(gp[LP], axis=1) == np.sort(LP[gl], axis=1)).all()
    return 'LINES PRESERVED' if ok else 'lines moved'
rng = np.random.default_rng(5)
def rand_sl3():
    while True:
        A = rng.integers(0, q, (3, 3))
        if int(round(np.linalg.det(A))) % q == 1 and round(np.linalg.det(A)) != 0:
            return A
# pairs (0,4), (1,5), (2,6)
pairs = [(0, 4), (1, 5), (2, 6)]
for choice in itertools.product([0, 1], repeat=3):
    Wc = [pairs[i][choice[i]] for i in range(3)]
    Wd = [pairs[i][1 - choice[i]] for i in range(3)]
    g = rand_sl3()
    print('W =', Wc, 'partners', Wd, ':', test(block_act(g, Wc, Wd)))
