import sys, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c4')
from mult import *
q = int(sys.argv[1])
N, LP, PL, coord = load(q)
adj = build_adj(N, LP, PL)
W = mult_voltages(q, N, LP, coord, spec=0)
print('q', q, 'N', N, 'W sample', W[0], W[1])
rng = random.Random(5)
for d in [x for x in range(2, q - 1) if (q - 1) % x == 0] + [q - 1]:
    Wd = W % d
    m1 = measure(q, d, Wd, LP, PL, N, adj, trials=200, rng=random.Random(7))
    # random voltages uniform in Z_d (independent per flag)
    Rnd = np.random.default_rng(3).integers(0, d, size=W.shape)
    m2 = measure(q, d, Rnd, LP, PL, N, adj, trials=200, rng=random.Random(7))
    print(f'd={d}: mult distinct sums pts/lines {m1}   random {m2}', flush=True)
