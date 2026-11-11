# usage: mkfrob.py m k r OUT.bin  -- multiplication table of Z_m x|_r Z_k, element (i,j) -> i*k+j,
# (i1,j1)(i2,j2) = (i1 + r^{j1} i2 mod m, j1+j2 mod k). Format for exh3: int32 N, then N*N uint16 T[g*N+h].
import sys, numpy as np
m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
N = m * k
rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
idx = np.arange(N, dtype=np.int64)
i1, j1 = idx // k, idx % k
T = np.empty((N, N), dtype=np.uint16)
for g in range(N):
    I2 = idx // k; J2 = idx % k
    ii = (i1[g] + rp[j1[g]] * I2) % m
    jj = (j1[g] + J2) % k
    T[g, :] = (ii * k + jj).astype(np.uint16)
with open(sys.argv[4], 'wb') as f:
    f.write(np.int32(N).tobytes()); f.write(T.tobytes())
