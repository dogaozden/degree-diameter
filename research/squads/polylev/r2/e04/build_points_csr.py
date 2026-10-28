"""Full collinearity graph of H(13) (402234 points, 182 neighbours each) in mis2 CSR format: work/P_{n,off,nb}.bin."""
import struct, numpy as np
HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q13.bin'
WORK = '/home/user/degree-diameter/research/squads/polylev/r2/e04/work'
with open(HEX, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).astype(np.int64)
flat = lines.ravel()
order = np.argsort(flat, kind='stable')
PL = (order // (q + 1)).reshape(N, q + 1)
nb = np.empty((N, q * (q + 1)), dtype=np.int32)
CH = 20000
for c0 in range(0, N, CH):
    v = np.arange(c0, min(N, c0 + CH))
    nbm = lines[PL[v]].reshape(len(v), (q + 1) * (q + 1))
    mask = nbm != v[:, None]
    nb[c0:c0 + len(v)] = nbm[mask].reshape(len(v), q * (q + 1))
np.array([N], dtype=np.int32).tofile(WORK + '/P_n.bin')
(np.arange(N + 1, dtype=np.int64) * (q * (q + 1))).astype(np.int32).tofile(WORK + '/P_off.bin')
nb.tofile(WORK + '/P_nb.bin')
print('point graph written', N, nb.shape, flush=True)
