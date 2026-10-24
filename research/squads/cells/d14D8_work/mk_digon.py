"""Digon design: two disjoint perfect matchings F_1, F_2 of the incidence graph of H(q) (each point matched to two of
its own lines); the extra edge of a matched flag runs parallel to the hexagon edge.
Voltages in Z_5 x Z_t (CRT into Z_{5t}) or plain Z_m:
  mode z5t: hexagon (0, phi) with phi random in Z_t; extra edge of F_j flag: (s_j, phi + delta), delta random.
  mode rand: all voltages uniform in Z_m.
python3 mk_digon.py q m seed mode out"""
import sys, numpy as np
import subprocess
from hexlib import load, write_base, hex_edges
q, m, seed, mode, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
# random relabelling so the matchings are not biased by ids
perm = rng.permutation(N)
used = np.zeros((N, q + 1), dtype=bool)  # used[p, k]: flag (p, PL[p,k]) taken
M = []
for j in range(2):
    A = np.where(used, -1, PL)
    inp = f"{N} {q + 1}\n" + "\n".join(" ".join(map(str, r)) for r in A.tolist()) + "\n"
    res = subprocess.run(['./pmatch', str(seed * 7 + j)], input=inp.encode(), capture_output=True, check=True)
    Mj = np.array(res.stdout.split(), dtype=np.int64)
    pos = np.argmax(PL == Mj[:, None], axis=1)
    assert (PL[np.arange(N), pos] == Mj).all() and not used[np.arange(N), pos].any()
    used[np.arange(N), pos] = True
    M.append(Mj)
H = hex_edges(LP)
if mode == 'z5t':
    t = m // 5; assert m % 5 == 0 and t % 5
    e5 = next(x for x in range(m) if x % 5 == 1 and x % t == 0); et = next(x for x in range(m) if x % 5 == 0 and x % t == 1)
    phi = rng.integers(0, t, len(H)); H[:, 2] = (phi * et) % m
    # phi of a flag (p, l): need lookup: H rows are (LP[l, k], l) in order l-major
    flag_phi = {}
    E = [H]
    Hl = H[:, 1].reshape(N, q + 1); Hp = H[:, 0].reshape(N, q + 1); Hv = phi.reshape(N, q + 1)
    for j, s in enumerate((1, 2)):
        l = M[j]; kpos = np.argmax(LP[l] == np.arange(N)[:, None], axis=1)
        ph = Hv[l, kpos]
        de = rng.integers(0, t, N)
        E.append(np.stack([np.arange(N), l, (s * e5 + (ph + de) * et) % m], axis=1))
else:
    H[:, 2] = rng.integers(0, m, len(H)); E = [H]
    for j in range(2):
        E.append(np.stack([np.arange(N), M[j], rng.integers(0, m, N)], axis=1))
write_base(out, N, m, np.concatenate(E))
print('ok', file=sys.stderr)
