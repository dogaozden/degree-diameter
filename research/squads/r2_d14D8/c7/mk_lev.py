"""Level designs: lift group Z_L x Z_k (CRT into Z_{Lk}, gcd(L,k)=1). Hex flags (0, h), jumps (s_j, c_j(p)) along
bijections phi_j. python3 mk_lev.py q L k seed s1,s2 hexmode jumpmode phimode out
hexmode: zero | rand ; jumpmode: zero | rand ; phimode: same (one bijection doubled) | indep"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, write_base, hex_edges
q, L, k, seed = map(int, sys.argv[1:5]); shifts = [int(x) for x in sys.argv[5].split(',')]
hexmode, jumpmode, phimode, out = sys.argv[6:10]
m = L * k
from math import gcd; assert gcd(L, k) == 1
def crt(a, b):  # a mod L, b mod k -> Z_m
    for x in range(m):
        pass
    return None
T = np.zeros((L, k), dtype=np.int64)
for x in range(m): T[x % L, x % k] = x
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
hv = np.zeros(LP.shape, dtype=np.int64) if hexmode == 'zero' else rng.integers(0, k, LP.shape)
E = [hex_edges(LP, T[0, hv])]
phi = rng.permutation(N)
for s in shifts:
    if phimode == 'indep': phi = rng.permutation(N)
    c = np.zeros(N, dtype=np.int64) if jumpmode == 'zero' else rng.integers(0, k, N)
    E.append(np.stack([np.arange(N), phi, T[s % L, c]], axis=1))
write_base(out, N, m, np.concatenate(E))
