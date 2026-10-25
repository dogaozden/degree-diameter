import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo
G = Geo(8)
MUL, INV = G.MUL, G.INV
C = G.C
P = C[:, [0, 1, 2, 4, 5, 6]].astype(np.int64)   # standard 6-coords, w = u0v3+u3v0+u1v4+u4v1+u2v5+u5v2
N = P.shape[0]
SIG = [3, 4, 5, 0, 1, 2]   # w(u,y) = XOR_k MUL[u_k, y_{SIG[k]}]
def w_row(u):
    """w(u, P_j) for all j, u a 6-vector (GF(8) ints)"""
    r = np.zeros(N, dtype=np.int64)
    for k in range(6):
        r ^= MUL[u[k], P[:, SIG[k]]]
    return r
def w_pair(u, v):
    r = 0
    for k in range(6): r ^= int(MUL[u[k], v[SIG[k]]])
    return r
def normalize6(v):
    v = [int(x) for x in v]
    for x in v:
        if x:
            inv = int(INV[x]); break
    return tuple(int(MUL[inv, y]) for y in v)
KEY = {tuple(int(x) for x in P[i]): i for i in range(N)}
def id_of6(v):
    return KEY[normalize6(v)]
def mat_apply(M, v):
    out = []
    for i in range(6):
        s = 0
        for k in range(6): s ^= int(MUL[M[i][k], v[k]])
        out.append(s)
    return out
def load_set(path):
    return [int(t) for t in open(path).read().split()]
def check_sym():
    rng = np.random.default_rng(0)
    for _ in range(200):
        i, j = rng.integers(N, size=2)
        assert (w_pair(P[i], P[j]) != 0) == (G.B(C[i:i+1], C[j:j+1])[0, 0] != 0)
    return True
