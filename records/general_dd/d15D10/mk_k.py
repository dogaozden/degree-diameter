#!/usr/bin/env python3
"""mk_k.py IN OUT k : wrap a cay_mg group file Q into Q x Z_k (header p, -L0, k) for cay_mgk."""
import sys, struct
src, out, k = sys.argv[1], sys.argv[2], int(sys.argv[3])
b = open(src, 'rb').read(); p, L = struct.unpack('ii', b[:8]); assert L > 0
open(out, 'wb').write(struct.pack('iii', p, -L, k) + b[8:])
