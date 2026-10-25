#!/usr/bin/env python3
"""Card c4 (squad round 4): greedy deficit trajectories from the 720 set.
State: A = pairwise-opposite outside points, N(A) = S points blocking some a in A.  The solution S' = (S minus N(A)) plus A
is pairwise opposite with |S'| = 720 - |N(A)| + |A|.  Each step adds the outside point z, opposite to every point of A,
with the fewest NEW blockers (ties random).  The best value |A| - |N(A)| along each trajectory is recorded; a positive value
is a gain and is written to OUT_IDX.
usage: greedy_deficit.py SEED CPU_SECONDS STEPS [OUT_IDX]"""
import sys, os, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L

seed, cpus, steps = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
out_path = sys.argv[4] if len(sys.argv) > 4 else os.path.join(HERE, 'runs', 'greedy_gain_idx.txt')
rng = np.random.default_rng(seed)
S = np.loadtxt(os.path.join(HERE, 'init720_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
PJ = L.PJ; P = L.P; N = L.N
inS = np.zeros(N, bool); inS[S] = True
Mb = np.zeros((N, S.size), bool)               # Mb[y, i] = 1 iff S-point i blocks y (B = 0), y != S[i]
for i, s in enumerate(S.tolist()):
    z = ((PJ @ P[s]) % 11) == 0
    z[s] = False
    Mb[:, i] = z
outside = np.flatnonzero(~inS)
Mo = Mb[outside].astype(np.float32)           # blocker matrix of outside points (float for matvec)
cnt_out = Mo.sum(axis=1)
seeds_pool = outside[cnt_out <= 60]
print('blocker matrix built', Mo.shape, 'seed pool', seeds_pool.size, flush=True)
t0 = time.process_time()
best_val, best_A, trials = 0, None, 0
while time.process_time() - t0 < cpus:
    trials += 1
    y = int(rng.choice(seeds_pool))
    A = [y]
    blockedA = (PJ @ P[y]) % 11 == 0          # outside points not opposite to y (incl. y)
    cover = Mb[y].astype(np.int32)
    val_traj = []
    for step in range(steps):
        val = len(A) - int((cover > 0).sum())
        val_traj.append(val)
        if val > best_val:
            best_val, best_A = val, list(A)
            print(f'trial {trials}: gain {val} at |A|={len(A)}', flush=True)
        unc = (cover == 0).astype(np.float32)
        newc = Mo @ unc                             # new blockers of every outside point
        ok = ~blockedA[outside]
        if not ok.any():
            break
        newc = np.where(ok, newc, np.inf)
        mn = newc.min()
        pick = rng.choice(np.flatnonzero(newc == mn))
        z = int(outside[pick])
        A.append(z)
        cover += Mb[z]
        blockedA |= (PJ @ P[z]) % 11 == 0
    print(f'trial {trials}: |A| {len(A)} |N| {int((cover > 0).sum())} max value along trajectory {max(val_traj)}', flush=True)
print('done trials', trials, 'best gain', best_val, flush=True)
if best_A is not None and best_val > 0:
    Nset = np.flatnonzero(np.any(Mb[best_A], axis=0))
    Sprime = np.concatenate([np.setdiff1d(S, S[Nset]), np.array(best_A)])
    np.savetxt(out_path, np.sort(Sprime), fmt='%d', header=f'# {Sprime.size} points, greedy deficit gain')
    print('wrote', out_path, Sprime.size, flush=True)
