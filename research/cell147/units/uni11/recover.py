# Which stored permutation (data/perms_q11) has the 240-set as a union of cycles, and what isometry induces it?
import sys, glob
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r3/c3')
from orth import *
pos = {int(a): i for i, a in enumerate(pid)}
S = set(pos[int(l.split()[0])] for l in open('../sols/flags_q11_orbit4_240.txt'))
def solve(A, b):
    # solve A x = b mod p (A square, invertible)
    n = A.shape[0]; M_ = np.concatenate([A % p, (b % p).reshape(n, -1)], axis=1)
    for c in range(n):
        piv = next(i for i in range(c, n) if M_[i, c])
        M_[[c, piv]] = M_[[piv, c]]; M_[c] = (M_[c] * INV[M_[c, c]]) % p
        for i in range(n):
            if i != c and M_[i, c]: M_[i] = (M_[i] - M_[i, c] * M_[c]) % p
    return M_[:, n:]
def recover(perm):
    rng = np.random.default_rng(0)
    while True:
        idx = rng.choice(N, 7, replace=False)
        B = U[idx[:6]].T % p                       # columns = basis points
        try: c = solve(B, U[idx[6]])[:, 0]
        except StopIteration: continue
        if np.any(c == 0): continue
        Bp = U[perm[idx[:6]]].T % p
        try: d = solve(Bp, U[perm[idx[6]]])[:, 0]
        except StopIteration: continue
        lam = (d * INV[c]) % p                     # h b_i = lam_i b'_i (up to common scalar)
        H = (Bp * lam[None, :]) % p
        h = (H @ solve(B, np.eye(6, dtype=np.int64))) % p
        if np.array_equal(perm_of(h), perm): return h
for f in sorted(glob.glob('../../data/perms_q11/*.txt')):
    perm = np.loadtxt(f, dtype=np.int64)
    cyc = cycles(perm)
    ok = all((set(c) <= S) or not (set(c) & S) for c in cyc)
    if ok:
        h = recover(perm)
        print(f, "240-set is a union of cycles; h =\n", h)
        np.save('h240.npy', h)
