"""Generators for the twist annealer: random elements of G_2(q) (short random words in SL(3,q) and long root
elations), every one checked to be a collineation of H(q).  Writes int32 G, n, then G x (point perm, line perm).
usage: gens.py hex_qQ.txt G out.bin [seed] [wordlen]"""
import sys, random, numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0] if '/' in __file__ else '.')
from geo import Hex
from mktwist import rand_elem
H = Hex(sys.argv[1]); G = int(sys.argv[2]); rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 7)
wl = int(sys.argv[5]) if len(sys.argv) > 5 else 3
with open(sys.argv[3], 'wb') as f:
    np.array([G, H.n], dtype=np.int32).tofile(f)
    for i in range(G):
        p, l = H.perm(rand_elem(H, rng, wl)); p.astype(np.int32).tofile(f); l.astype(np.int32).tofile(f)
print('wrote', G, 'generators')
