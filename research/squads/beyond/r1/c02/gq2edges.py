# Convert a gqgen bin (int32 q,N,L; L*(q+1) int32 point ids; N*7 uint8 coords) into an apsp edge list.
# Vertices: points 0..N-1, lines N..N+L-1. Usage: python3 gq2edges.py gq_qX.bin out.edges
import sys, struct
import numpy as np
fn, out = sys.argv[1], sys.argv[2]
with open(fn, 'rb') as f:
    q, N, L = struct.unpack('<iii', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype='<i4').reshape(L, q + 1)
assert lines.min() >= 0 and lines.max() < N
with open(out, 'w') as g:
    g.write(f'{N + L}\n')
    for j in range(L):
        for p in lines[j]:
            g.write(f'{int(p)} {N + j}\n')
print(f'q={q} points={N} lines={L} vertices={N+L} edges={L*(q+1)}')
