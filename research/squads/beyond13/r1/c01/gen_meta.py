import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/tools')
import groups
m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
out = sys.argv[4]
T = groups.t_meta(m, k, r)
N = m * k
with open(out, 'wb') as f:
    f.write(np.array([N], dtype=np.int32).tobytes()); f.write(T.astype(np.uint16).tobytes())
