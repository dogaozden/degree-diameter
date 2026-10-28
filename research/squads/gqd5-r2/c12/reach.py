"""c12: count vertex pairs at distance > 5 via boolean matrix powers (numpy, float32 BLAS)."""
import numpy as np
def far_pairs(n, E):
    A = np.zeros((n, n), dtype=np.float32)
    for a, b in E:
        A[a, b] = 1; A[b, a] = 1
    R = A + np.eye(n, dtype=np.float32)
    R2 = (R @ R > 0).astype(np.float32)
    R4 = (R2 @ R2 > 0).astype(np.float32)
    R5 = (R4 @ R > 0)
    return ~R5   # True where distance > 5 (or disconnected)
