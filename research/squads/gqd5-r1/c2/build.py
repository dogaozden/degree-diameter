"""Build W(11) once and cache point vectors and collinearity matrix."""
import sys, os, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
t = time.time()
G = gqlib.W(11)
print('built', G.np, G.nl, time.time() - t, flush=True)
P = np.array(G.coords, dtype=np.int64)
np.savez('/home/user/degree-diameter/research/squads/gqd5-r1/c2/w11.npz', P=P, col=G.col)
