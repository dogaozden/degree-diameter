# c4: L-model (Z_37449, c2's gf.py) -> hex point id map, saved as L2H.npy; plus the translation-by-73 permutation check
import numpy as np, sys
from iso import hex_tuple, load_hex_proj
d, P = load_hex_proj()
M = np.array([d[hex_tuple(L)] for L in range(37449)], dtype=np.int64)
assert len(set(M.tolist())) == 37449
np.save('L2H.npy', M)
print('saved L2H.npy')
