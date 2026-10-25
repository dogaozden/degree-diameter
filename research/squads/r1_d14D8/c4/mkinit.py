import sys
import numpy as np
seed, m, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rng = np.random.default_rng(seed)
q = np.loadtxt('/home/user/degree-diameter/research/squads/r1_d14D8/c4/qstruct_1.txt', dtype=np.int64, skiprows=1)
w = rng.integers(0, m, len(q))
np.savetxt(out, np.column_stack([q, w]), fmt='%d')
print('wrote', out, len(q))
