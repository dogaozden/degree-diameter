# assoc_check.py TABLE : random associativity, identity and inverse checks of a groups.py-format table (int32 N, uint16 N*N)
import sys, random, struct
import numpy as np
data = open(sys.argv[1], 'rb').read()
N = struct.unpack('<i', data[:4])[0]
T = np.frombuffer(data[4:4 + 2 * N * N], dtype='<u2').reshape(N, N).astype(np.int64)
rng = np.random.default_rng(1)
x = rng.integers(0, N, 300000); y = rng.integers(0, N, 300000); z = rng.integers(0, N, 300000)
assoc = np.all(T[T[x, y], z] == T[x, T[y, z]])
ident = np.all(T[0, np.arange(N)] == np.arange(N)) and np.all(T[np.arange(N), 0] == np.arange(N))
inv = all((T[np.arange(N), :] == 0).any(axis=1))
print(f"N={N} random_assoc={assoc} identity_ok={ident} every_row_has_inverse={inv}")
