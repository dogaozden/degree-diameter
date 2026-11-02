import numpy as np, sys
# read hex/hex_q3.bin -> base edge list (points 0..N-1, lines N..N+L-1)
d = np.fromfile(sys.argv[1], dtype=np.int32)
q, N, L = int(d[0]), int(d[1]), int(d[2])
inc = d[3:3+L*(q+1)].reshape(L, q+1)
V = N + L
edges = []
for l in range(L):
    for p in inc[l]:
        edges.append((int(p), N + l))
E = np.array(edges, dtype=np.int64)
with open(sys.argv[2], 'w') as f:
    f.write(f"{V} {len(E)}\n")
    for a, b in E: f.write(f"{a} {b}\n")
print("V", V, "E", len(E), "deg check", np.bincount(E.ravel(), minlength=V).min(), np.bincount(E.ravel(), minlength=V).max())
