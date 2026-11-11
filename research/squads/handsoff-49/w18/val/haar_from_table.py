# haar_from_table.py TABLE S... OUT : Haar graph H(G,S) (edges (g,A)~(s g,B), s in S) from a groups.py table; writes an edge list
import sys, struct
import numpy as np
tab, out = sys.argv[1], sys.argv[-1]
S = [int(x) for x in sys.argv[2:-1]]
data = open(tab, 'rb').read()
N = struct.unpack('<i', data[:4])[0]
T = np.frombuffer(data[4:4 + 2 * N * N], dtype='<u2').reshape(N, N).astype(np.int64)
with open(out, 'w') as f:
    f.write(f"{2 * N}\n")
    for s in S:
        for g in range(N):
            f.write(f"{g} {N + int(T[s, g])}\n")
print('wrote', out, 'N', N, 'S', S)
