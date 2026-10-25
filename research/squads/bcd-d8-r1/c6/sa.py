"""c6 SA: voltage-only moves (tau-invariant voltages), pi and rho fixed by seed. Score = bcd --cost."""
import sys, time, math
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/bcd-d8-r1/c6')
import base2 as b
M = int(sys.argv[1]); seed = int(sys.argv[2]); iters = int(sys.argv[3]); T0 = float(sys.argv[4]); tlimit = float(sys.argv[5])
rng = np.random.default_rng(seed)
pi = b.equiv_perm(b.H.porb, b.H.ppos, b.H.prep, rng, b.TP)
rho = b.equiv_perm(b.H.lorb, b.H.lpos, b.H.lrep, rng, b.TL)
E, inv, nk = b.build_edges(pi, rho)
w = rng.integers(0, M, nk)
tag = f'sa_{M}_{seed}'
path = f'{b.HERE}/{tag}.spec'
b.write_spec(path, M, E, inv, w)
cur = b.cost(path); best = cur; bestw = w.copy()
print('start', cur, flush=True)
t0 = time.time()
for it in range(iters):
    if time.time() - t0 > tlimit: break
    T = T0 * (1 - it / iters) + 0.3
    k = rng.integers(nk)
    old = w[k]
    w[k] = (old + rng.integers(1, M)) % M
    b.write_spec(path, M, E, inv, w)
    c = b.cost(path)
    d = c - cur
    if d <= 0 or rng.random() < math.exp(-d / T):
        cur = c
        if c < best:
            best = c; bestw = w.copy()
            print('it', it, 'best', best, 'T', round(T, 2), 'time', round(time.time() - t0), flush=True)
        if best == 0:
            break
    else:
        w[k] = old
print('final best', best, 'iters', it + 1, 'time', round(time.time() - t0), flush=True)
b.write_spec(f'{b.HERE}/{tag}_best.spec', M, E, inv, bestw)
np.save(f'{b.HERE}/{tag}_best_w.npy', bestw)
np.save(f'{b.HERE}/{tag}_pi.npy', pi); np.save(f'{b.HERE}/{tag}_rho.npy', rho)
