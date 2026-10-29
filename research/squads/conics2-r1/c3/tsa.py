import sys, time, math, random
import numpy as np
from common import *
from ls import pts_near_point
from srcdist import graph_T, dist_from

if __name__ == '__main__':
    seed = int(sys.argv[1]); x = int(sys.argv[2]); budget = float(sys.argv[3]); out = sys.argv[4]
    T0 = float(sys.argv[5]) if len(sys.argv) > 5 else 2.0
    rng = random.Random(seed)
    sig, R0 = load_rec()
    R = list(R0) + [x]; Rset = set(R)
    G2 = pts_near_point(x, 2); G2s = set(G2)
    G4 = [j for j in pts_near_point(x, 4) if j not in G2s]
    sinv = np.empty(N, np.int64)
    bad = score(sig, R); best = (bad, sig.copy()); t0 = time.time(); it = 0; acc = 0
    print('start bad', bad, flush=True)
    while time.time() - t0 < budget and best[0] > 0:
        it += 1
        sinv[sig] = np.arange(N)
        T = T0 * max(0.05, 1 - (time.time() - t0) / budget)
        dist = dist_from(graph_T(sig, R), x)
        miss = [v - 2 * N for v in range(2 * N, 3 * N) if dist[v] > 7]
        if not miss:
            break
        v = rng.choice(miss)                       # uncovered level-1 point
        l = rng.choice(list(PL[v]))                # a line through v
        qo = int(sinv[l])                          # current owner of line l
        p = rng.choice(G2) if rng.random() < 0.6 else rng.choice(G4)
        if p == qo or (p in Rset and qo in Rset):
            continue
        sig2 = sig.copy(); sig2[p], sig2[qo] = sig2[qo], sig2[p]
        bad2 = score(sig2, R)
        d = bad2 - bad
        if d <= 0 or rng.random() < math.exp(-d / T):
            sig, bad = sig2, bad2; acc += 1
            if bad < best[0]:
                best = (bad, sig.copy()); save(best[1], R, out)
                print(f'it {it} t={time.time()-t0:.0f}s best {bad}', flush=True)
        if it % 50 == 0:
            print(f'it {it} t={time.time()-t0:.0f}s cur {bad} best {best[0]} acc {acc}', flush=True)
    print('done it', it, 'best', best[0], 'time', round(time.time() - t0), 'acc', acc, flush=True)
    save(best[1], R, out)
