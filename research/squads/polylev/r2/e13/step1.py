import sys, time
import numpy as np
from common import *
q = int(sys.argv[1])
t = time.time()
H = load(q)
B = ball_matrix_cached(H, q)
print('q', q, 'N', H.N, 'lines', H.L, 'ball sizes', set(B.sum(1).tolist()), 'time', round(time.time() - t, 1))
