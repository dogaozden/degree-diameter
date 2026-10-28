"""singer_perms.py: a Singer element g of SL(3,q) (order q^2+q+1) acting on H(q) by (v,a,w) -> (gv, a, g^-T w);
writes the point and line permutations of g^e for a given exponent e (e.g. q=9: e=7 gives order 13, e=13 order 7).
Usage: python3 singer_perms.py HEXBIN e OUTPREFIX [seed]"""
import sys, numpy as np
from hexlib import Hex
from spreadpart import find_singer, mat_pow
H = Hex(sys.argv[1]); e = int(sys.argv[2]); out = sys.argv[3]
rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
g = find_singer(H, rng); ge = mat_pow(H, g, e)
pm = H.sl3_point_map(ge); lm = H.line_map(pm)
o = 1; x = pm[0]
while x != 0: x = pm[x]; o += 1
pm.astype(np.int32).tofile(out + '.pperm'); lm.astype(np.int32).tofile(out + '.lperm'); np.savetxt(out + '.g', ge, fmt='%d')
print('order of g^%d on point 0: %d' % (e, o))
