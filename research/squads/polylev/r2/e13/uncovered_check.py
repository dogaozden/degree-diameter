"""Lines not covered by the pencil set; does some subset of them (size q+1 = 5) dominate all lines (4-ball)?
Also tries the 5-subsets of the uncovered lines for a valid extra class. Usage: uncovered_check.py POINTS.npy"""
import sys, itertools
import numpy as np
from common import *
H = load(4)
B = ball_matrix_cached(H, 4)
S = np.load(sys.argv[1]).tolist()
cov = np.zeros(H.L, bool)
for p in S:
    cov[H.PL[p]] = True
U = [int(x) for x in np.nonzero(~cov)[0]]
print('pencil points', len(S), 'uncovered lines', len(U), U)
good = []
for T in itertools.combinations(U, 5):
    if B[list(T)].any(axis=0).all():
        good.append(T)
print('uncovered 5-subsets that 4-dominate all lines:', len(good), good[:5])
# also: how many lines does each uncovered line 4-see among U
print('pairwise distance-4 structure of U (1 = within distance 4):')
print(np.array([[int(B[a, b]) for b in U] for a in U]))
