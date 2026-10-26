import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load
N, LP, PL, coord = load(5)
B = np.zeros((N, N), dtype=np.float32)
B[LP.reshape(-1), np.repeat(np.arange(N), 6)] = 1.0   # rows points, cols lines
G = B.T @ B                                          # line-line: common points
A = G - 6 * np.eye(N, dtype=np.float32)
ev = np.linalg.eigvalsh(A.astype(np.float64))
vals, cnt = np.unique(np.round(ev, 6), return_counts=True)
print('distinct eigenvalues of line-concurrence graph:', list(zip(vals.tolist(), cnt.tolist())))
lmin = ev.min(); k = 30
print('Hoffman bound alpha <=', N * (-lmin) / (k - lmin), 'needed 558')
