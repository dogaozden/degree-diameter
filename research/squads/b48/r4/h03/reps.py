# h03: write "N R rep..." (conjugacy class representatives of a group table, as element indices) for gen
import sys, numpy as np
fn = sys.argv[1]
N = int(np.fromfile(fn, dtype=np.int32, count=1)[0])
T = np.fromfile(fn, dtype=np.uint16, offset=4).reshape(N, N).astype(np.int64)
inv = np.array([int(np.where(T[x] == 0)[0][0]) for x in range(N)])
C = T[T, inv[:, None]]          # C[x,g] = x g x^-1
reps = np.unique(C.min(axis=0))
print(N, len(reps), *reps.tolist())
