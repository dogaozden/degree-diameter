# c5 analysis: structure of the 397 set (elliptic ovoid at infinity + lines in direction u).
import struct, sys
import numpy as np
path = '/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin'
raw = open(path, 'rb').read()
q, N, L = struct.unpack('<iii', raw[:12])
co = np.frombuffer(raw[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
p = 11
S = [int(l) for l in open('/home/user/degree-diameter/research/squads/d13D7_r2/c6/best_idx.txt') if l.strip() and not l.startswith('#')]
inf_all = np.where(co[:, 0] == 0)[0]
# candidate elliptic section: infinity points with y5 = 2*y1 (mod 11)
sec = inf_all[(co[inf_all, 5] - 2 * co[inf_all, 1]) % p == 0]
print('points at infinity', len(inf_all), ' with y5=2*y1:', len(sec))
S_inf = [i for i in S if co[i, 0] == 0]
print('397-set infinity points:', len(S_inf), ' all inside section:', all(i in set(sec.tolist()) for i in S_inf))
np.save('/home/user/degree-diameter/research/squads/d13D7_r3/c5/sec122.npy', sec)
