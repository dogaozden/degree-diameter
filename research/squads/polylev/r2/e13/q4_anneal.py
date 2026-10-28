"""q=4: search for NON-pencil 4-dominating 5-sets of lines by annealing on the number of undominated lines.
Cost = #lines L with no chosen line in Ball4(L). Pencils are rejected (all 5 lines through one point).
Usage: q4_anneal.py SEED SECONDS"""
import sys, time
import numpy as np
from common import *
seed, secs = int(sys.argv[1]), float(sys.argv[2])
rng = np.random.default_rng(seed)
H = load(4)
B = ball_matrix_cached(H, 4)
L = H.L
def cost(S):
    return int((~B[:, S].any(axis=1)).sum())
def is_pencil(S):
    c = set(H.lines[S[0]].tolist())
    for m in S[1:]:
        c &= set(H.lines[m].tolist())
    return len(c) > 0
t0 = time.time()
best_overall = None
found = []
restarts = 0
while time.time() - t0 < secs and len(found) < 5:
    restarts += 1
    S = list(rng.choice(L, 5, replace=False))
    c = cost(S)
    T = 2.0
    for it in range(20000):
        i = int(rng.integers(5))
        new = int(rng.integers(L))
        if new in S:
            continue
        S2 = S.copy(); S2[i] = new
        c2 = cost(S2)
        if c2 <= c or rng.random() < np.exp((c - c2) / T):
            S, c = S2, c2
        T = max(0.05, T * 0.9997)
        if c == 0:
            if not is_pencil(S):
                found.append(sorted(int(x) for x in S))
                print('non-pencil dominating 5-set:', sorted(int(x) for x in S), 'restart', restarts, flush=True)
            break
    if best_overall is None or c < best_overall[0]:
        best_overall = (c, sorted(int(x) for x in S))
print('restarts', restarts, 'found non-pencil', len(found), 'best cost seen', best_overall, 'time', round(time.time() - t0))
np.save(f'q4_nonpencil_anneal_s{seed}.npy', np.array(found, dtype=np.int64) if found else np.zeros((0, 5), dtype=np.int64))
