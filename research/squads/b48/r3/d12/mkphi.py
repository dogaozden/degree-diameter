# usage: mkphi.py TABLE.bin PHI.bin RULE M
# RULE j: phi(a + m*j) = j mod 2 ; RULE a: phi = a mod 2 (a = index % m)
import sys, numpy as np
path, out, rule, m = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
with open(path, 'rb') as f:
    N = int(np.frombuffer(f.read(4), dtype=np.int32)[0])
    T = np.frombuffer(f.read(), dtype=np.uint16).reshape(N, N)
idx = np.arange(N)
phi = ((idx // m) % 2) if rule == 'j' else ((idx % m) % 2)
phi = phi.astype(np.uint8)
ok = True
for x in range(0, N, 3):
    if not np.array_equal(phi[T[x].astype(np.int64)], phi[x] ^ phi):
        ok = False; break
print('homomorphism', ok, 'N', N, 'ones', int(phi.sum()))
if not ok: sys.exit(1)
phi.tofile(out)
