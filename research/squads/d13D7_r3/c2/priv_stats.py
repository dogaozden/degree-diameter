# card c2: structure of the 364 seed (blocking counts, private neighbours of each R point), numpy only
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
N = len(coord)
idx = [int(l) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
R = np.array(idx)
C = coord.astype(np.int64)
# B(x, r) for all x and r in R
Bm = np.zeros((N, len(R)), dtype=np.int64)
for j, r in enumerate(R):
    Bm[:, j] = hexlib.bilinear(C, C[r][None, :], q)[:, 0] if False else (
        C[:, 0]*C[r,4] + C[:,4]*C[r,0] + C[:,1]*C[r,5] + C[:,5]*C[r,1] + C[:,2]*C[r,6] + C[:,6]*C[r,2] - 2*C[:,3]*C[r,3]) % q
inR = np.zeros(N, dtype=bool); inR[R] = True
zero = (Bm == 0)
for j, r in enumerate(R):
    zero[r, j] = False
cnt = zero.sum(axis=1)
priv = np.zeros(len(R), dtype=int)
for j in range(len(R)):
    priv[j] = int(((cnt == 1) & zero[:, j] & ~inR).sum())
print('priv1 per R point: max', priv.max(), 'mean %.2f' % priv.mean(), 'hist', np.bincount(priv).tolist()[:12])
low = np.where((~inR) & (cnt <= 5) & (cnt >= 1))[0]
print('non-R points with cnt<=5:', len(low))
# blockers of the cnt<=5 points: how many distinct R points are involved
bl = set()
for x in low:
    bl.update(R[zero[x]].tolist())
print('distinct blockers of cnt<=5 points:', len(bl))
