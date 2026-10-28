"""Anneal the matchings of all transitions except t0 so that the whole level graph (no hubs) has no pair at distance > 5.
Usage: anneal.py r s steps seed [T0]   (R on t0=(0,1) is a random s-subset of points, M_t0 a random bijection, fixed)."""
import sys, time, math, pickle, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c19')
from common import *
r, s, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
T0 = float(sys.argv[5]) if len(sys.argv) > 5 else 2.0
G = gqlib.Q4(5)
g = Graph(G, r)
rng = np.random.default_rng(seed)
t0 = (0, 1)
M = {t: rng.permutation(G.np) for t in g.trans}
R = {t0: set(rng.choice(G.np, s, replace=False).tolist())}
others = [t for t in g.trans if t != t0]
cur = g.bad(M, R)
best = cur; bestM = {t: M[t].copy() for t in M}
print('start', cur, flush=True)
t_start = time.time()
for it in range(steps):
    T = T0 * (1 - it / steps) + 0.05
    t = others[rng.integers(len(others))]
    a, b = rng.choice(G.np, 2, replace=False)
    M[t][a], M[t][b] = M[t][b], M[t][a]
    new = g.bad(M, R)
    d = new - cur
    if d <= 0 or rng.random() < math.exp(-d / T):
        cur = new
        if cur < best:
            best = cur; bestM = {tt: M[tt].copy() for tt in M}
            if best == 0:
                break
    else:
        M[t][a], M[t][b] = M[t][b], M[t][a]
    if it % 500 == 0:
        print('it', it, 'cur', cur, 'best', best, 'T %.2f' % T, 'elapsed %.0f' % (time.time() - t_start), flush=True)
print('FINAL r=%d s=%d seed=%d best=%d' % (r, s, seed, best), flush=True)
pickle.dump({'r': r, 's': s, 'best': best, 'M': bestM, 'R': R, 't0': t0}, open('/home/user/degree-diameter/research/squads/gqd5-r1/c19/state_r%d_s%d_seed%d.pkl' % (r, s, seed), 'wb'))
