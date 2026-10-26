"""Simulated annealing over the Z_k parts of hexagon flags and matchings, exact cost = GCOST of gcheck (range:0:2N)."""
import sys, numpy as np, time, math, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c7')
from lift import *
q, k, iters, seed, T0, T1 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6])
tag = f'anneal_q{q}_k{k}_s{seed}'
N, LP, sig = make_base(q, 1)
rng = np.random.default_rng(seed)
hb = rng.integers(0, k, N*(q+1)); mb = rng.integers(0, k, (2, N))
path = f'/home/user/degree-diameter/research/squads/r1_d8c/c7/runs/{tag}.txt'
def cost(hb, mb):
    write_lift(q, k, hb, mb, sig, path)
    c, _ = run_gcheck(path, 2*N)
    return c
cur = cost(hb, mb); best = cur; bestst = (hb.copy(), mb.copy())
t0 = time.time(); nv = N*(q+1) + 2*N
for it in range(iters):
    T = T0 * (T1/T0) ** (it/iters)
    v = rng.integers(nv)
    old = None
    if v < N*(q+1):
        old = hb[v]; hb[v] = (old + rng.integers(1, k)) % k
    else:
        j = v - N*(q+1); t, p = divmod(j, N); old = mb[t, p]; mb[t, p] = (old + rng.integers(1, k)) % k
    new = cost(hb, mb)
    if new is not None and (new <= cur or rng.random() < math.exp(-(new-cur)/T)):
        cur = new
        if cur < best:
            best = cur; bestst = (hb.copy(), mb.copy())
            print('it', it, 'best', best, 'T %.2f' % T, 'time %.0f' % (time.time()-t0), flush=True)
        if cur == 0: break
    else:
        if v < N*(q+1): hb[v] = old
        else: mb[t, p] = old
    if it % 200 == 0: print('it', it, 'cur', cur, 'best', best, 'T %.2f' % T, 'time %.0f' % (time.time()-t0), flush=True)
    if time.time() - t0 > float(sys.argv[7]): break
np.savez(f'/home/user/degree-diameter/research/squads/r1_d8c/c7/runs/{tag}_best.npz', hb=bestst[0], mb=bestst[1])
print('FINAL best', best, 'iters', it+1, flush=True)
