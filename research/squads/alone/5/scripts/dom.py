# how many B-centres does greedy need to radius-3 dominate all of A? (base flag graph)
import numpy as np
from cov import greedy_cover
C = np.load('C3.npy')
cov = np.zeros(C.shape[1], dtype=bool); chosen = []
while not cov.all():
    gains = (C & ~cov).sum(axis=1)
    b = int(np.argmax(gains)); chosen.append(b); cov |= C[b]
    if len(chosen) in (8, 12, 16, 18, 20, 22, 24, 26, 28, 30) or cov.all():
        print('centres', len(chosen), 'uncovered', int((~cov).sum()), flush=True)
print('greedy domination number <=', len(chosen))
