#!/usr/bin/env python3
"""Lift a fibration set to points of H(11) for the scorer oppcheck.
Affine chart: the points opposite e4 = (0,0,0,0,1,0,0) are x = (1, a, b, c, c^2 - a e - b f, e, f), (a,b,c,e,f) in F_11^5,
and B(x, x') = Q'(x - x') with Q'(a,b,c,e,f) = c^2 - a e - b f.  Given a direction u (Q'(u) != 0) and offsets t, the set
e4 + {t + lam*u : lam in F_11} is pairwise opposite iff every two offsets t, t' have Q'(t - t' + lam*u) != 0 for all lam.
usage: fiblift.py U OFFSETS OUT_IDX [OUT_COORDS]
  U: five numbers "a b c e f" (quoted), e.g. "1 0 0 9 0" (Q'(u) = 2, the round-1 direction)
  OFFSETS: one offset "a b c e f" per line ('#' lines ignored); the lift writes e4 and the 11 points of each line
  (also accepts full points: a line with 7 numbers is taken as a point of H(11) and copied as is)."""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hexlib
q, lines, coord = hexlib.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hex', 'hex_q11.bin'))
code = coord @ (q ** np.arange(7))
u = np.array([int(t) for t in sys.argv[1].split()]) % q
pts = [np.array([0, 0, 0, 0, 1, 0, 0])]
for s in open(sys.argv[2]):
    s = s.strip()
    if not s or s.startswith('#'):
        continue
    v = np.array([int(t) for t in s.split()]) % q
    if len(v) == 7:
        pts.append(v); continue
    for lam in range(q if u.any() else 1):
        a, b, c, e, f = (v + lam * u) % q
        pts.append(np.array([1, a, b, c, (c * c - a * e - b * f) % q, e, f]))
idx = []
for x in pts:
    nz = np.nonzero(x)[0][0]
    x = (x * pow(int(x[nz]), q - 2, q)) % q
    k = int(x @ (q ** np.arange(7)))
    j = int(np.searchsorted(code, k))
    assert code[j] == k, 'not a point of Q(6,11)'
    idx.append(j)
idx = sorted(set(idx))
with open(sys.argv[3], 'w') as f:
    f.write(f'# {len(idx)} points, fiblift u = {sys.argv[1]}\n' + '\n'.join(map(str, idx)) + '\n')
if len(sys.argv) > 4:
    with open(sys.argv[4], 'w') as f:
        f.write(f'# {len(idx)} points (coordinates x0..x6), fiblift u = {sys.argv[1]}\n')
        for j in idx:
            f.write(' '.join(map(str, coord[j].tolist())) + '\n')
print(f'{len(idx)} points written to {sys.argv[3]}')
