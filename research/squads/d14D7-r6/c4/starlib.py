import numpy as np, sys, os, random, time, collections, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
H = Hex(SP + 'hex_q11.bin'); N = H.N; q = H.q
R = np.load(SP + 'R756idx.npy').astype(np.int64); S = np.load(SP + 'S_herm.npy').astype(np.int64)
Sidx = -np.ones(N, dtype=np.int64); Sidx[S] = np.arange(len(S))
inS = Sidx >= 0
def line_pts(u, v):
    U = H.X[u]; V = H.X[v]
    vecs = [(U + lam * V) % q for lam in range(q)] + [V]
    return H.index_of(np.array(vecs))
def profile(L):
    """(index of the unique S-line meeting L (-1 if L in S), boolean array over S of distance-4 lines)"""
    d2, d4 = H.line_ball(int(L))
    d2 = np.fromiter(d2, dtype=np.int64); d4 = np.fromiter(d4, dtype=np.int64)
    conc = Sidx[d2]; conc = conc[conc >= 0]
    D4 = np.zeros(len(S), bool); x = Sidx[d4]; D4[x[x >= 0]] = True
    return conc, D4
def base_T_codes(T):
    """for each base point: -1 if orthogonal to all of T (T-perp), else index in T of its unique orthogonal point,
    or -2 if it is orthogonal to none (cannot happen for a line T: a hyperplane always meets T)"""
    orth = (H.Bmat(R, T) == 0)
    cnt = orth.sum(axis=1)
    code = np.where(cnt == len(T), -1, np.argmax(orth, axis=1))
    return code
