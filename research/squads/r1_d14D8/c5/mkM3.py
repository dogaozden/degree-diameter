"""Perfect matching M3 with every M-pair at hexagon distance 3 (sampled candidates + Hopcroft-Karp).
Usage: python3 mkM3.py SEED OUT.npy [D]"""
import sys, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load
HERE = '/home/user/degree-diameter/research/squads/r1_d14D8/c5'
seed, out = int(sys.argv[1]), sys.argv[2]
D = int(sys.argv[3]) if len(sys.argv) > 3 else 40
N, LP, PL, coord = load(13)
rng = np.random.default_rng(seed)
cand = np.empty((N, D), dtype=np.int64)
pts = np.arange(N)
for j in range(D):
    k1 = rng.integers(0, 14, N); k2 = rng.integers(0, 14, N); k3 = rng.integers(0, 14, N)
    l1 = PL[pts, k1]                       # line through p
    x = LP[l1, k2]                         # point on that line
    l2 = PL[x, k3]                         # line through x
    cand[:, j] = l2
# distance-3 lines are those not incident to p; resample the bad ones (incident lines) by rejection
for it in range(50):
    inc = np.zeros((N, D), dtype=bool)
    for j in range(D):
        inc[:, j] = (PL[pts, :] == cand[:, j:j + 1]).any(axis=1)
    if not inc.any():
        break
    k1 = rng.integers(0, 14, N); k2 = rng.integers(0, 14, N); k3 = rng.integers(0, 14, N)
    fresh = PL[LP[PL[pts, k1], k2], k3]
    cand[inc] = fresh[np.nonzero(inc)[0]]
inc = np.zeros((N, D), dtype=bool)
for j in range(D):
    inc[:, j] = (PL[pts, :] == cand[:, j:j + 1]).any(axis=1)
print('incident candidates left', int(inc.sum()), file=sys.stderr)
with open(f'{HERE}/work/cand_{seed}.bin', 'wb') as f:
    np.array([N, D], dtype=np.int32).tofile(f)
    cand.astype(np.int32).tofile(f)
r = subprocess.run([HERE + '/hk', f'{HERE}/work/cand_{seed}.bin', f'{HERE}/work/M3raw_{seed}.bin', str(seed)],
                   capture_output=True, text=True)
sys.stderr.write(r.stderr[-300:])
assert r.returncode == 0, 'matching failed'
M = np.fromfile(f'{HERE}/work/M3raw_{seed}.bin', dtype=np.int32).astype(np.int64)
np.save(out, M)
# check distances on a sample: all M-pairs non-incident
bad = (PL == M[:, None]).any(axis=1).sum()
print('M3 written; incident pairs', int(bad), 'perm ok', len(set(M.tolist())) == N, file=sys.stderr)
