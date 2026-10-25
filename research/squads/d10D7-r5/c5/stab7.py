import numpy as np, sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from h7 import *
q, N, lines, coords = load_hex(HEX7)
S = np.array([int(x) for x in open('/home/user/degree-diameter/research/squads/d10D7-r4/c5/points_best.txt').read().split()])
print('q', q, 'N', N, 'lines', lines.shape, 'S', len(S), 'distinct', len(set(S.tolist())))
X = coords[S]
print('on quadric:', bool((qval(X, q) == 0).all()))
BS = Bmat(X, X, q)
off = BS[~np.eye(len(S), dtype=bool)]
print('pairwise B nonzero off-diagonal:', bool((off != 0).all()), 'rank mod 7:', None)
# rank over GF(7)
def rank_mod(M, p):
    M = M.copy() % p; r = 0; rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c] % p: piv = i; break
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        M[r] = (M[r] * inv) % p
        for i in range(rows):
            if i != r and M[i, c]: M[i] = (M[i] - M[i, c] * M[r]) % p
        r += 1
    return r
print('rank of S as vectors mod 7:', rank_mod(X, q))
# code -> point id for normalized vectors
pw = 7 ** np.arange(7)
codes = coords @ pw
idx = np.full(7 ** 7, -1, dtype=np.int64); idx[codes] = np.arange(N)
np.save('/home/user/degree-diameter/research/squads/d10D7-r5/c5/idx7.npy', idx)
