"""c02 sample.py: sample Hermitian spreads S_v of H(9) = lines of H(9) contained in v^perp (polar form b of the
quadric, as in g2.gram_row / spreadT.py), keep those with exactly q^3+1 = 730 lines, dedup, save.
Output: OUT.npz with S (M x 730 int32, sorted line ids per row), V (M x 7 int8 vectors v).
Usage: python3 sample.py SEED TARGET SECONDS OUT.npz"""
import os, sys, time
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
import numpy as np
from hexlib import Hex
from g2 import gram_row

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q9.bin'
seed, target, secs, out = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
H = Hex(HEX)
q, N = H.q, H.N
assert q == 9
rng = np.random.default_rng(seed)
LA, LB = H.lines[:, 0], H.lines[:, 1]
C = H.coord
want = q ** 3 + 1
seen = {}
S_list, V_list = [], []
tries = 0
sizes = {}
t0 = time.time()
while len(S_list) < target and time.time() - t0 < secs:
    v = rng.integers(0, q, size=7)
    if not v.any():
        continue
    tries += 1
    y = gram_row(H, v)
    B = np.zeros(N, dtype=np.int64)
    for j in range(7):
        B = H.ADD[B, H.MUL[y[j], C[:, j]]]
    # a line lies in v^perp iff both of its points are orthogonal to v (the form is linear)
    S = np.flatnonzero((B[LA] == 0) & (B[LB] == 0))
    sizes[len(S)] = sizes.get(len(S), 0) + 1
    if len(S) != want:
        continue
    key = S.astype(np.int32).tobytes()
    if key in seen:
        continue
    seen[key] = len(S_list)
    S_list.append(S.astype(np.int32))
    V_list.append(v.astype(np.int8))
    if len(S_list) % 500 == 0:
        print('spreads', len(S_list), 'tries', tries, 'secs', round(time.time() - t0), flush=True)
S = np.array(S_list, dtype=np.int32)
V = np.array(V_list, dtype=np.int8)
np.savez(out, S=S, V=V)
print('done: distinct spreads', len(S), 'tries', tries, 'secs', round(time.time() - t0, 1))
print('line-count histogram over tries (count: tries):', dict(sorted(sizes.items(), key=lambda kv: -kv[1])[:12]))
