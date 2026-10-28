"""lines2ids.py: convert a list of totally singular lines given by coordinates (binary: int32 q, int32 count, then
count x (q+1) x 7 uint8 normalised coordinates, the format of squad card r2/e03) into the text format of d11cert.py
(one class per text line: the q+1 point ids). Usage: python3 lines2ids.py HEXBIN IN.bin OUT.txt"""
import sys
import numpy as np
from hexlib import Hex

H = Hex(sys.argv[1])
raw = open(sys.argv[2], 'rb').read()
q, cnt = np.frombuffer(raw[:8], dtype=np.int32)
assert q == H.q
X = np.frombuffer(raw[8:], dtype=np.uint8).reshape(cnt, q + 1, 7).astype(np.int64)
ids = H.point_ids(X.reshape(-1, 7)).reshape(cnt, q + 1)
np.savetxt(sys.argv[3], ids, fmt='%d')
print(f'{cnt} lines converted')
