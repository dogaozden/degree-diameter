# Elliptic quadric Q(z)=Tr_{q^6/q}(c * z^{q^3+1}) on GF(7^6); fibers of the norm = candidate ovoids.
import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r4/c5')
p, n, q = 7, 6, 7
Q6, M = 7**6, 7**6 - 1
exp = np.load('/home/user/degree-diameter/research/squads/d10D7-r4/c5/gf76_exp.npy')
LOG = np.full(Q6, -1, dtype=np.int64); LOG[exp] = np.arange(M)
pw7 = np.array([7**i for i in range(6)], dtype=np.int64)
D = np.stack([(np.arange(Q6) // 7**i) % 7 for i in range(6)], axis=1)   # digits of each code
def fadd(a, b):
    return (((D[a] + D[b]) % 7) * pw7).sum(axis=-1)
def trace_code(K):
    """Tr_{q^6/q}(exp[K]) as an element of F_7 (returns int array); K array of logs (mod M)."""
    tot = np.zeros(K.shape, dtype=np.int64)
    for i in range(6):
        tot = fadd(tot, exp[(K * 7**i) % M])
    assert (D[tot][..., 1:] == 0).all(), 'trace not in F_7'
    return D[tot][..., 0]
def Qvals_logs(L, Lc):
    """Q(z) for z = exp[L] (L array of logs, z != 0)."""
    K = (L * 344 + Lc) % M
    return trace_code(K)
def Qcodes(codes, Lc):
    out = np.zeros(codes.shape, dtype=np.int64)
    nz = codes != 0
    out[nz] = Qvals_logs(LOG[codes[nz]], Lc)
    return out
if __name__ == '__main__':
    allL = np.arange(M)
    res = {}
    for k in range(0, 60):
        pass
    # try several c = exp[Lc]; count singular nonzero vectors
    for Lc in [0, 1, 2, 3, 5, 7, 11, 13, 17, 19]:
        Qv = Qvals_logs(allL, Lc)
        nsing = int((Qv == 0).sum())
        print('Lc', Lc, 'singular nonzero vectors', nsing, '(elliptic 16512, hyperbolic 17100)')
