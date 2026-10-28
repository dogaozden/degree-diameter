"""expandT.py: expand an independent set of the t.s.-line orbit quotient (tsorbq.c) into the list of its lines
(one line per text row: q+1 point ids, the class format of d11cert.py).
Usage: python3 expandT.py PREFIX PPERM Q SOLUTION OUT"""
import sys
import numpy as np
pre, pp, q, sol, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
pm = np.fromfile(pp, dtype=np.int32).astype(np.int64)
reps = np.fromfile(pre + '.reps', dtype=np.int32).reshape(-1, q + 1).astype(np.int64)
osz = np.fromfile(pre + '.osz', dtype=np.int32)
S = np.array(open(sol).read().split(), dtype=np.int64)
rows = []
for v in S:
    x = reps[v]
    for _ in range(osz[v]):
        rows.append(x.copy()); x = pm[x]
np.savetxt(out, np.array(rows), fmt='%d')
print(f'{len(S)} orbits -> {len(rows)} lines')
