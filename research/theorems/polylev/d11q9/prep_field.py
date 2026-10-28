"""prep_field.py HEXBIN OUT: dump field tables and point coordinates for ils_lines.c.
Layout: int32 q, N; ADD (q*q int32); MUL (q*q int32); NEG (q int32); INV (q int32); coords (N*7 uint8)."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
from hexlib import Hex

H = Hex(sys.argv[1])
q, N = H.q, H.N
with open(sys.argv[2], 'wb') as f:
    np.array([q, N], dtype=np.int32).tofile(f)
    H.ADD.astype(np.int32).tofile(f)
    H.MUL.astype(np.int32).tofile(f)
    H.NEG.astype(np.int32).tofile(f)
    H.INV.astype(np.int32).tofile(f)
    H.coord.astype(np.uint8).tofile(f)
print('q', q, 'N', N, 'wrote', sys.argv[2])
