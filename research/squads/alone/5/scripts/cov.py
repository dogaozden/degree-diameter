# radius-3 coverage of the A side by B-centred balls, via sparse matrices (flag-graph ids: A < nA <= B)
import sys, numpy as np, scipy.sparse as sp, time
from graph import load
def biadj(path):
    n, adj, E = load(path)
    nA = n // 2
    rows = np.array([u for u, v in E]); cols = np.array([v - nA for u, v in E])
    M = sp.csr_matrix((np.ones(len(E), dtype=np.int32), (rows, cols)), shape=(nA, nA))
    return n, nA, M, E
def ball3_B(M):
    """C[b, a] = 1 iff dist(a, b) <= 3 for a in A, b in B (dense bool, rows=B)"""
    Mt = M.T.tocsr()
    D2 = (Mt @ M).tocsr()            # B-B paths of length 2
    D3 = (D2 @ Mt).tocsr()            # B-A paths of length 3 (counted)
    C = (Mt + D3).tocsr()
    C.data[:] = 1
    return C.toarray().astype(bool)
def greedy_cover(C, k, rnd=None, start=None):
    cov = np.zeros(C.shape[1], dtype=bool); chosen = []
    for _ in range(k):
        gains = (C & ~cov).sum(axis=1)
        b = int(np.argmax(gains)) if rnd is None else int(rnd.choice(np.flatnonzero(gains >= gains.max() - 2)))
        chosen.append(b); cov |= C[b]
    return chosen, int((~cov).sum())
if __name__ == '__main__':
    t = time.time()
    n, nA, M, E = biadj(sys.argv[1])
    C = ball3_B(M)
    print('ball3 row sizes', set(C.sum(axis=1).tolist()), 'time', round(time.time() - t, 1), flush=True)
    chosen, unc = greedy_cover(C, 16)
    print('greedy 16: uncovered', unc, 'chosen', chosen)
    np.save('C3.npy', C)
