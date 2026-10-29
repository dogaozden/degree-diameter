import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
from hexload import load
q, N, LP, PL, X = load('/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q5.bin')
A = np.load('A.npy')
P2 = (A @ A.T) > 0.5; np.fill_diagonal(P2, False)
LL = (A.T @ A) > 0.5; np.fill_diagonal(LL, False)
nb = np.array([np.nonzero(P2[x])[0] for x in range(N)], dtype=np.int32)
assert nb.shape == (N, 30)
nb.tofile('nbr.bin')
LL.astype(np.uint8).tofile('LL.bin')
# record sigma as plain list
lines = open('/home/user/degree-diameter/research/frontier/sols/d7D7_hex5_mirror81_n23598.sol').read().split('\n')
sig = np.array([int(t) for s in lines[3:] for t in s.split()], dtype=np.int64)
sig.astype(np.int32).tofile('sig_record.bin')
R = np.array([int(t) for t in lines[1].split()[1:]])
np.savetxt('R_record.txt', R, fmt='%d')
print('ok', nb.shape, LL.sum())
