"""Write TABLE.bin (int32 N, then N*N uint16, T[s*N+g] = index of s*g, identity 0) for meta m k r."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/tools')
import groups
m, k, r, fn = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
T = groups.table(f"meta {m} {k} {r}")
N = m * k
with open(fn, 'wb') as f:
    f.write(np.array([N], dtype=np.int32).tobytes()); f.write(T.astype(np.uint16).tobytes())
print("wrote", fn, N)
