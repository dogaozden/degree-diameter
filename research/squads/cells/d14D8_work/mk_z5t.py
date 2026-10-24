"""Z_5 x Z_t design (CRT into Z_{5t}, gcd(5,t)=1): hexagon edges carry (0, phi), phi random in Z_t;
matching j carries (s_j, alpha_j(x)), s = (1, 2), alpha random in Z_t (or 0).
python3 mk_z5t.py q t seed alphamode out   (alphamode: 0 = alpha 0, 1 = random)"""
import sys, numpy as np
from hexlib import load, write_base, hex_edges
q, t, seed, am, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
m = 5 * t
assert t % 5
# CRT: x = a*e5 + b*et with e5 = 1 mod 5, 0 mod t ; et = 0 mod 5, 1 mod t
e5 = next(x for x in range(m) if x % 5 == 1 and x % t == 0)
et = next(x for x in range(m) if x % 5 == 0 and x % t == 1)
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
H = hex_edges(LP); H[:, 2] = (rng.integers(0, t, len(H)) * et) % m
E = [H]
for s in (1, 2):
    M = rng.permutation(N)
    al = rng.integers(0, t, N) if am else np.zeros(N, dtype=np.int64)
    E.append(np.stack([np.arange(N), M, (s * e5 + al * et) % m], axis=1))
write_base(out, N, m, np.concatenate(E))
