# c2: map abstract classes (npy of L in Z_37449) to hex_q8 point ids and write a plain id file
import numpy as np, sys
from iso import hex_tuple, load_hex_proj
src, dst = sys.argv[1], sys.argv[2]
L = np.load(src)
d, P = load_hex_proj()
ids = [d[hex_tuple(int(x))] for x in L]
assert len(set(ids)) == len(ids)
open(dst, 'w').write(' '.join(map(str, sorted(ids))) + '\n')
print('wrote', len(ids), 'ids to', dst)
