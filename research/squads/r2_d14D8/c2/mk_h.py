"""mk_h.py q k hsrc aseed bseed out [phiseed]   (squad r2_d14D8, card c2)
Level family (Z_5 levels x Z_k sub-levels, lift group Z_m, m = 5k):
  hex flags (p, l) get voltage T(0, h[flag]); one seeded bijection phi: points -> lines carries
  (p, phi(p)) with T(1, a(p)) and a second (p, phi(p)) with T(2, b(p)); a, b uniform on Z_k (seeded).
  T: Z_5 x Z_k -> Z_m by CRT when gcd(5, k) = 1 (k = 6, 7); for k = 5 (m = 25, not a CRT case) T(l, s) = l + 5 s.
hsrc: 'rand:SEED' (uniform h) or a file with L lines of q+1 integers (hv[l*(q+1)+j] = voltage of flag at line l,
position j), the layout written by bundle.c."""
import sys
from math import gcd
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, write_base, hex_edges
q, k = int(sys.argv[1]), int(sys.argv[2]); hsrc = sys.argv[3]
aseed, bseed, out = int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
phiseed = int(sys.argv[7]) if len(sys.argv) > 7 else 1
Lv = 5; m = Lv * k
T = np.zeros((Lv, k), dtype=np.int64)
if gcd(Lv, k) == 1:
    for x in range(m): T[x % Lv, x % k] = x
else:
    for l in range(Lv):
        for s in range(k): T[l, s] = l + Lv * s
assert len(set(T.reshape(-1).tolist())) == m
N, LP, PL, coord = load(q)
if hsrc.startswith('rand:'):
    hv = np.random.default_rng(int(hsrc[5:])).integers(0, k, LP.shape)
else:
    hv = np.loadtxt(hsrc, dtype=np.int64).reshape(LP.shape) % k
a = np.random.default_rng(aseed).integers(0, k, N)
b = np.random.default_rng(bseed).integers(0, k, N)
phi = np.random.default_rng(phiseed).permutation(N)
E = [hex_edges(LP, T[0, hv])]
E.append(np.stack([np.arange(N), phi, T[1, a]], axis=1))
E.append(np.stack([np.arange(N), phi, T[2, b]], axis=1))
write_base(out, N, m, np.concatenate(E))
print(f'wrote {out}: q={q} k={k} m={m} N={N} edges={sum(len(e) for e in E)}')
