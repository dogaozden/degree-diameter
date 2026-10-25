#!/usr/bin/env python3
"""Card c4 (squad round 4): orbit structure of the 720 set under its group <a,b> (generators in init720_gen.txt)."""
import sys, os
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L
from replay2 import read_gens

desc, gens = read_gens(os.path.join(HERE, 'init720_gen.txt'))
S = np.loadtxt(os.path.join(HERE, 'init720_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
perms = [L.perm_of(g) for g in gens]
lab = L.orbit_labels(perms)
sizes = np.bincount(lab)
print('group:', desc, '| #gens', len(gens), '| orbits', sizes.size)
print('orbit size histogram:', {int(k): int(v) for k, v in zip(*np.unique(sizes, return_counts=True))})
labs_S = np.unique(lab[S])
print('S uses', labs_S.size, 'orbits; sizes', sorted(sizes[labs_S].tolist()))
union = np.flatnonzero(np.isin(lab, labs_S))
print('S is a union of orbits:', np.array_equal(np.sort(union), np.sort(S)))
np.save(os.path.join(HERE, 'lab720.npy'), lab)
np.save(os.path.join(HERE, 'labs_S720.npy'), labs_S)
