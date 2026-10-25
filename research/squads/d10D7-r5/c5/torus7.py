# c5: torus-orbit model for H(7): T = diag(A, 1, A^{-T}) with A = diag(A_lam, 1) on (x0,x1,x2), lam primitive in GF(49).
# Orbits of <T> on the points of Q(6,7); compatibility = all cross pairs non-perpendicular.
import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from h7 import *
q, N, lines, coords = load_hex(HEX7)
pw = 7 ** np.arange(7)
idx = np.full(7 ** 7, -1, dtype=np.int64); idx[coords @ pw] = np.arange(N)
INV = np.array([0, 1, 4, 5, 2, 3, 6])
def mat_inv_mod(M, p):
    n = M.shape[0]; A = np.concatenate([M % p, np.eye(n, dtype=np.int64)], axis=1)
    for c in range(n):
        piv = [i for i in range(c, n) if A[i, c] % p][0]
        A[[c, piv]] = A[[piv, c]]
        A[c] = (A[c] * pow(int(A[c, c]), p - 2, p)) % p
        for i in range(n):
            if i != c and A[i, c]: A[i] = (A[i] - A[i, c] * A[c]) % p
    return A[:, n:]
def torus_matrix(s, t, n_nr=3, p=7):
    # A_lam for lam = s + t*w, w^2 = n_nr
    Alam = np.array([[s, t * n_nr], [t, s]]) % p
    A = np.eye(3, dtype=np.int64); A[:2, :2] = Alam
    T = np.zeros((7, 7), dtype=np.int64)
    # coordinates: index order (x0,x1,x2,x3,x4,x5,x6)
    Ainv_T = mat_inv_mod(A, p).T % p
    U = [0, 1, 2]; Up = [4, 5, 6]
    for i in range(3):
        for j in range(3):
            T[U[i], U[j]] = A[i, j]
            T[Up[i], Up[j]] = Ainv_T[i, j]
    T[3, 3] = 1
    return T % p
def order_proj(M, p=7):
    P = M.copy() % p; k = 1
    I = np.eye(7, dtype=np.int64)
    def pn(X):
        f = X.flatten(); nz = np.nonzero(f)[0][0]; return (X * INV[f[nz]]) % p
    Pn = pn(P); In = pn(I)
    while not np.array_equal(Pn, In):
        P = (P @ M) % p; Pn = pn(P); k += 1
        if k > 100000: return -1
    return k
def perm_of(M, p=7):
    Y = (coords @ M.T) % p
    nz = Y != 0
    first = np.argmax(nz, axis=1)
    lead = Y[np.arange(N), first]
    Yn = (Y * INV[lead][:, None]) % p
    return idx[Yn @ pw]
if __name__ == '__main__':
    # find lam of order 48 in GF(49)
    best = None
    for s in range(7):
        for t in range(1, 7):
            T = torus_matrix(s, t)
            o = order_proj(T)
            if o == 48:
                best = (s, t, T); break
        if best: break
    s, t, T = best
    print('lam = %d + %d w, order of projective T:' % (s, t), order_proj(T))
    pi = perm_of(T)
    assert (pi >= 0).all()
    # orbits of pi
    seen = np.zeros(N, bool); orbits = []
    for x in range(N):
        if seen[x]: continue
        orb = []; y = x
        while not seen[y]:
            seen[y] = True; orb.append(y); y = pi[y]
        orbits.append(orb)
    from collections import Counter
    print('orbit sizes:', sorted(Counter(len(o) for o in orbits).items()))
    np.save('/home/user/degree-diameter/research/squads/d10D7-r5/c5/torus7_T.npy', T)
    import pickle
    pickle.dump(orbits, open('/home/user/degree-diameter/research/squads/d10D7-r5/c5/torus7_orbits.pkl', 'wb'))
