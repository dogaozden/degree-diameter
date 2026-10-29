import numpy as np
from common import *
D = q + 2
def graph_T(sig, R):
    sig = np.asarray(sig, np.int64)
    free = np.zeros(N, bool); free[np.asarray(sorted(R), np.int64)] = True
    T = np.full((4 * N, D), -1, np.int64)
    T[:N, :q + 1] = PL + N; T[N:2 * N, :q + 1] = LP; T[2 * N:3 * N, :q + 1] = PL + 3 * N; T[3 * N:, :q + 1] = LP + 2 * N
    keep = np.nonzero(~free)[0]
    T[keep, q + 1] = 3 * N + sig[keep]
    sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N)
    lk = 3 * N + np.arange(N); ok = ~free[sinv]
    T[lk[ok], q + 1] = sinv[ok]
    T[T < 0] = -1
    return T
def dist_from(T, s):
    dist = np.full(4 * N, 99, np.int64); dist[s] = 0; front = np.array([s])
    d = 0
    while len(front):
        d += 1
        nb = T[front].reshape(-1); nb = nb[nb >= 0]
        nb = np.unique(nb[dist[nb] == 99])
        dist[nb] = d; front = nb
    return dist
