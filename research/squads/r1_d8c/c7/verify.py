"""Rebuild the saved best state (npz) as an explicit lift file for an independent all-pairs check."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c7')
from lift import *
q, k, npz, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
N, LP, sig = make_base(q, 1)
d = np.load(npz)
print(write_lift(q, k, d['hb'], d['mb'], sig, out))
