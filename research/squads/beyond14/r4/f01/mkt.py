import sys
import numpy as np
# mkt.py OUT m k r : table of Z_m x|_r Z_k in the own-small format ("G N 1 name", then N rows; index 0 = identity)
out, m, k, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
assert pow(r, k, m) == 1 % m
N = m * k
R = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
x = np.arange(N, dtype=np.int64)
a, j = x // k, x % k
X, Y = x[:, None], x[None, :]
A, J = a[:, None], j[:, None]
B, L = a[None, :], j[None, :]
T = (((A + R[J] * B) % m) * k + (J + L) % k).astype(np.int64)
assert (T[0] == x).all() and (T[:, 0] == x).all()
rng = np.random.default_rng(1)
s = rng.integers(0, N, (3, 20000))
assert (T[T[s[0], s[1]], s[2]] == T[s[0], T[s[1], s[2]]]).all()
with open(out, 'w') as f:
    f.write(f"G {N} 1 Z{m}x{r}Z{k}\n")
    np.savetxt(f, T, fmt='%d')
print("ok", N)
