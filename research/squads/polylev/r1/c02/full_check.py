"""c02 full_check.py: exhaustive check of one base Hermitian spread S0 = S_{v0} (first sampled spread) against
every projective hyperplane v' of PG(6,9) (597,870 of them). Overlap(v') = #{lines l of S0 : both points of l
are b-orthogonal to v'}, computed for all v' at once via the two designated points of each line of S0.
For v' with overlap 0, the full line count |S_{v'}| is computed; the spreads with 730 lines and overlap 0 are
the disjoint Hermitian spreads of S0. Usage: python3 full_check.py SPREADS.npz OUT.json"""
import os, sys, time, json
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/polylev')
import numpy as np
from hexlib import Hex
from g2 import gram_row
t0 = time.time()
H = Hex('/home/user/degree-diameter/research/theorems/polylev/hex/hex_q9.bin')
q, N = H.q, H.N
d = np.load(sys.argv[1]); S, V = d['S'], d['V']
out = sys.argv[2]
S0 = S[0].astype(np.int64)
v0 = V[0].astype(np.int64)
p0 = H.lines[S0, 0]; p1 = H.lines[S0, 1]
pts = np.empty(2 * len(S0), dtype=np.int64)
pts[0::2] = p0; pts[1::2] = p1
# y_p with b(v, p) = y_p . v  (gram_row is linear in its argument)
Y = np.array([gram_row(H, H.coord[p]) for p in pts], dtype=np.uint8)
ADD = H.ADD.astype(np.uint8); MUL = H.MUL.astype(np.uint8)
# all projective points: first nonzero coordinate equal to 1
rows = []
for k in range(7):
    free = 6 - k
    n = q ** free
    block = np.zeros((n, 7), dtype=np.uint8)
    block[:, k] = 1
    idx = np.arange(n)
    for t in range(free):
        block[:, k + 1 + t] = (idx // q ** t) % q
    rows.append(block)
P = np.concatenate(rows)
assert len(P) == (q ** 7 - 1) // (q - 1), len(P)
print('projective hyperplanes', len(P), 'base points', len(pts), flush=True)
hist = np.zeros(len(S0) + 1, dtype=np.int64)
zero_cands = []
CH = 8000
for s in range(0, len(P), CH):
    V_ = P[s:s + CH]
    acc = np.zeros((len(V_), len(pts)), dtype=np.uint8)
    for j in range(7):
        acc = ADD[acc, MUL[V_[:, j][:, None], Y[:, j][None, :]]]
    Z = (acc[:, 0::2] == 0) & (acc[:, 1::2] == 0)
    ov = Z.sum(axis=1)
    hist += np.bincount(ov, minlength=len(S0) + 1)[:len(S0) + 1]
    for i in np.flatnonzero(ov == 0):
        zero_cands.append(V_[i].astype(np.int64))
print('overlap histogram with S0 over all hyperplanes (overlap: count):',
      {int(k): int(v) for k, v in enumerate(hist) if v}, 'secs', round(time.time() - t0, 1), flush=True)
# full line count for overlap-0 hyperplanes
want = q ** 3 + 1
cnt = {}
disjoint_730 = []
for v in zero_cands:
    y = gram_row(H, v)
    B = np.zeros(N, dtype=np.int64)
    for j in range(7):
        B = H.ADD[B, H.MUL[y[j], H.coord[:, j]]]
    ln = int(((B[H.lines[:, 0]] == 0) & (B[H.lines[:, 1]] == 0)).sum())
    cnt[ln] = cnt.get(ln, 0) + 1
    if ln == want:
        disjoint_730.append(v.tolist())
print('overlap-0 hyperplanes', len(zero_cands), 'line counts of those:', cnt, flush=True)
print('disjoint Hermitian spreads (730 lines, overlap 0 with S0):', len(disjoint_730), flush=True)
res = {'base_v': v0.tolist(), 'base_index': 0, 'projective_hyperplanes': int(len(P)),
       'overlap_histogram_all_hyperplanes': {int(k): int(v) for k, v in enumerate(hist) if v},
       'overlap0_line_counts': {int(k): v for k, v in cnt.items()},
       'disjoint_730_count': len(disjoint_730), 'disjoint_730_vectors': disjoint_730[:10],
       'secs': round(time.time() - t0, 1)}
json.dump(res, open(out, 'w'), indent=1)
print('secs', round(time.time() - t0, 1))
