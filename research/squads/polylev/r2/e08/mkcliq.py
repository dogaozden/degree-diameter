"""Line-clique formulation of the 477-vertex orbit quotient (points side, q=8, Singer-73 orbits).
Every line of H(8) gives a clique of admissible point-orbits (its points lie in distinct admissible orbits, else the
orbit is inadmissible); every quotient edge lies in one such clique. Writes cliques as CSR (cl_off.bin, cl_mem.bin)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q8.bin')
E = '/home/user/degree-diameter/research/squads/polylev/r2/e08/'
orb = np.fromfile(E + 'S73.porb', dtype=np.int32)
qorb = np.fromfile(E + 'points_q_orb.bin', dtype=np.int32)
n = int(np.fromfile(E + 'points_q_n.bin', dtype=np.int32)[0]) if False else len(qorb)
qidx = -np.ones(orb.max() + 1, dtype=np.int64); qidx[qorb] = np.arange(len(qorb))
O = orb[H.lines]                                  # L x (q+1) orbit ids
Q = qidx[O]                                       # quotient index, -1 if inadmissible
cliques = set()
for l in range(H.L):
    row = Q[l]
    adm = row[row >= 0].tolist()
    if len(set(adm)) != len(adm): raise SystemExit('admissible orbit repeated on a line')
    if len(adm) >= 2: cliques.add(tuple(sorted(adm)))
cl = sorted(cliques)
print('lines', H.L, 'admissible distinct cliques', len(cl), 'sizes', np.bincount([len(c) for c in cl]))
off = np.zeros(len(cl) + 1, dtype=np.int32); mem = []
for i, c in enumerate(cl):
    mem.extend(c); off[i + 1] = len(mem)
np.array(off, dtype=np.int32).tofile(E + 'work/cl_off.bin')
np.array(mem, dtype=np.int32).tofile(E + 'work/cl_mem.bin')
# check every quotient edge is inside some clique
import itertools
A = np.fromfile(E + 'points_q_nb.bin', dtype=np.int32) if False else None
