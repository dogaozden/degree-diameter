# k-fixed tabu search for an independent set of size k in the orbit conflict graph (vertices = self-compatible orbits).
# usage: qtabu.py K SECONDS SEED OUTFILE
import pickle, sys, time
import numpy as np
K = int(sys.argv[1]); SECS = float(sys.argv[2]); SEED = int(sys.argv[3]); OUT = sys.argv[4]
d = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r5/c6/orb.pkl', 'rb'))
orbits, good, comp = d['orbits'], d['good'], d['comp']
n = len(good)
A = ~comp; np.fill_diagonal(A, False)          # conflict adjacency among good orbits
A = A.astype(np.int32)
rng = np.random.default_rng(SEED)
t0 = time.time(); best_out = None
it = 0
while time.time() - t0 < SECS:
    inS = np.zeros(n, bool)
    init = rng.choice(n, K, replace=False)
    inS[init] = True
    conf = A @ inS.astype(np.int32)
    tabu_in = np.zeros(n, np.int64); tabu_out = np.zeros(n, np.int64)
    tt = 7 + int(rng.integers(0, 5))
    best_f = None
    for step in range(200000):
        it += 1
        f = int(conf[inS].sum()) // 2
        if f == 0:
            best_out = np.nonzero(inS)[0]
            break
        # remove: conflicting vertex in S with max conf, non-tabu (random tie)
        cand = np.nonzero(inS & (conf > 0) & (tabu_out <= step))[0]
        if len(cand) == 0: cand = np.nonzero(inS & (conf > 0))[0]
        cu = conf[cand]; m = cu.max(); cu = cand[cu == m]
        u = int(cu[rng.integers(len(cu))])
        inS[u] = False; conf -= A[u]
        # add: vertex out of S minimising conf (non-tabu, random tie)
        score = conf.astype(np.float64) + rng.random(n) * 0.5
        score[inS] = 1e9
        score[tabu_in > step] = 1e9
        score[u] = 1e9 if tabu_in[u] > step else score[u]
        v = int(np.argmin(score))
        inS[v] = True; conf += A[v]
        tabu_in[u] = step + tt + int(rng.integers(0, 3))
        tabu_out[v] = step + 3
        if step % 2000 == 1999: tt = 7 + int(rng.integers(0, 5))
    if best_out is not None: break
    if time.time() - t0 > SECS: break
print('K', K, 'iters', it, 'time %.1f' % (time.time() - t0), 'found' if best_out is not None else 'NOT found')
if best_out is not None:
    pts = []
    for o in best_out:
        pts += orbits[good[o]]
    pts = sorted(pts)
    open(OUT, 'w').write('\n'.join(map(str, pts)) + '\n')
    print('wrote', len(pts), 'points to', OUT)
