"""c7 orbit tools for H(11): orbits of reflection groups, self-compatible orbits, compat matrix, unions."""
import sys, time, numpy as np, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/d10D7/ovoid/e7')
from grp11 import *
from mwc import max_weight_clique
CAP = 1332   # overwritten by run_e7q.py to q^3+1
def sc_and_compat(G, lab):
    q = G.q; C = G.C; no = lab.max() + 1
    members = [np.nonzero(lab == o)[0] for o in range(no)]
    S = []; okrep = {}
    for o, m in enumerate(members):
        if len(m) > CAP: continue
        r = m[0]
        ok = bform_mat(C[r][None, :], C[m], q)[0] != 0
        ok[0] = True                      # the representative itself (B(r,r)=0 by definition)
        if ok.all():
            S.append(o)
    # compat: rep of a against all points of b (opposite to all)
    n = len(S)
    if n == 0: return members, S, np.zeros((0, 0), bool)
    sizes = np.array([len(members[o]) for o in S])
    order = np.concatenate([members[o] for o in S]); starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    A = np.zeros((n, n), bool)
    for a, o in enumerate(S):
        r = members[o][0]
        ok = bform_mat(C[r][None, :], C[order], q)[0] != 0
        # each orbit b is compatible with a iff all its points are opposite to r (r rep of a)
        A[a] = np.logical_and.reduceat(ok, starts)
    A = A & A.T
    np.fill_diagonal(A, False)
    return members, S, A
def best_union(members, S, A, tl=60):
    n = len(S); w = [len(members[o]) for o in S]
    adj = [0] * n
    for i in range(n):
        bits = 0
        for j in np.nonzero(A[i])[0]: bits |= 1 << int(j)
        adj[i] = bits
    wgt, verts, done = max_weight_clique(w, adj, tl)
    return wgt, [S[i] for i in verts], done
