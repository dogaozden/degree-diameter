"""Independent recount of anti-homomorphism violations (numpy) for bijections given as line-index lists."""
import sys
import random
import numpy as np
N = 364
raw = np.fromfile('/home/user/degree-diameter/research/squads/r2-d8/d5/dist_q3.bin', dtype=np.uint8)
DP = raw[:N * N].reshape(N, N)
DL = raw[N * N:].reshape(N, N)
close_p = (DP == 2) | (DP == 4)
close_l = (DL == 2) | (DL == 4)
def viol(perm):
    perm = np.asarray(perm)
    sub = close_l[np.ix_(perm, perm)]
    return int(np.triu(close_p & sub, 1).sum())
rng = random.Random(5)
rp = list(range(N)); rng.shuffle(rp)
print('random perm violations', viol(rp))
for f in sys.argv[1:]:
    perm = [int(x) for x in open(f).read().split()]
    assert sorted(perm) == list(range(N))
    inc = np.load('/home/user/degree-diameter/research/squads/r2-d8/d5/inc_q3.npy')
    nin = sum(int(inc[p, perm[p]]) for p in range(N))
    print(f, 'violations', viol(perm), 'hops that are incidences', nin)
