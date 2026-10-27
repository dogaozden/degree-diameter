from base import *
import random, pickle
J = [[0,0,0,1,0,0],[0,0,0,0,1,0],[0,0,0,0,0,1],[1,0,0,0,0,0],[0,1,0,0,0,0],[0,0,1,0,0,0]]
def mm(A, B):
    R = [[0]*6 for _ in range(6)]
    for i in range(6):
        for j in range(6):
            s = 0
            for k in range(6): s ^= int(MUL[A[i][k], B[k][j]])
            R[i][j] = s
    return R
I6 = [[int(i == j) for j in range(6)] for i in range(6)]
def transvection(v, a):
    # x -> x + a w(x,v) v ; matrix I + a v (v^T J)   (w(x,v) = x^T J v)
    # row i of v^T J : (vJ)_j = sum_k v_k J[k][j]
    vJ = [0]*6
    for j in range(6):
        s = 0
        for k in range(6): 
            if J[k][j]: s ^= v[k]
        vJ[j] = s
    M = [[0]*6 for _ in range(6)]
    for i in range(6):
        for j in range(6):
            M[i][j] = I6[i][j] ^ int(MUL[a][int(MUL[v[i]][vJ[j]])])
    return M
def is_symp(M):
    # M^T J M == J
    MT = [[M[j][i] for j in range(6)] for i in range(6)]
    R = mm(mm(MT, J), M)
    return R == J
def mpow(M, k):
    R = I6; B = M
    while k:
        if k & 1: R = mm(R, B)
        B = mm(B, B); k >>= 1
    return R
def rand_symp(rng):
    M = I6
    for _ in range(40):
        v = [rng.randrange(8) for _ in range(6)]
        if not any(v): continue
        a = rng.randrange(1, 8)
        M = mm(transvection(v, a), M)
    return M
def perm_of(M):
    # point permutation: x -> M x  (acting on column vectors)
    out = np.zeros(N, dtype=np.int64)
    for i in range(N):
        out[i] = id_of6(mat_apply(M, [int(t) for t in P[i]]))
    return out
if __name__ == '__main__':
    rng = random.Random(12345)
    M0 = transvection([1,0,0,0,0,0], 1)
    assert is_symp(M0)
    found = None
    tries = 0
    while found is None and tries < 20000:
        tries += 1
        M = rand_symp(rng)
        assert is_symp(M)
        M513 = mpow(M, 513)
        if M513 == I6:
            ok = all(mpow(M, 513 // p) != I6 for p in (3, 19))
            if ok:
                found = M
    print('tries', tries, 'found', found is not None)
    if found is not None:
        pickle.dump(found, open('/home/user/degree-diameter/research/squads/hexfam_r1/c7/M513.pkl', 'wb'))
        print(found)
