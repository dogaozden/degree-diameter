import numpy as np
from abel import D
def enum_u_fast(k, R=D):
    U = np.zeros((1, 0), dtype=np.int64); nrm = np.zeros(1, dtype=np.int64)
    for _ in range(k):
        vals = np.arange(-R, R + 1, dtype=np.int64)
        nU = np.repeat(U, len(vals), axis=0)
        nn = np.repeat(nrm, len(vals)) + np.tile(np.abs(vals), len(U))
        col = np.tile(vals, len(U))
        keep = nn <= R
        U = np.hstack([nU[keep], col[keep][:, None]]); nrm = nn[keep]
    return U
