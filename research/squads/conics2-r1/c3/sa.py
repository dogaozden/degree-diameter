import sys, time, math, random
import numpy as np
from common import *
from ls import pts_near_point

if __name__ == '__main__':
    seed = int(sys.argv[1]); x = int(sys.argv[2]); budget = float(sys.argv[3]); out = sys.argv[4]
    T0 = float(sys.argv[5]) if len(sys.argv) > 5 else 4.0
    rng = random.Random(seed)
    sig0, R0 = load_rec()
    R = list(R0) + [x]
    sig = sig0.copy()
    G2 = pts_near_point(x, 2) ; G4 = [j for j in pts_near_point(x, 4) if j not in set(G2)]
    NB = G2 + G4
    bad = score(sig, R)
    best = (bad, sig.copy()); t0 = time.time(); it = 0; acc = 0
    print('start x=%d bad=%d |G2|=%d |G4|=%d' % (x, bad, len(G2), len(G4)), flush=True)
    Rset = set(R)
    while time.time() - t0 < budget and best[0] > 0:
        it += 1
        u = rng.random()
        if u < 0.4:
            a = rng.choice(G2)
        else:
            a = rng.choice(NB)
        if rng.random() < 0.8:
            b = rng.choice(NB)
        else:
            b = rng.randrange(N)
        if a == b or (a in Rset and b in Rset):
            continue
        sig2 = sig.copy(); sig2[a], sig2[b] = sig2[b], sig2[a]
        bad2 = score(sig2, R)
        d = bad2 - bad
        T = T0 * max(0.05, 1 - (time.time() - t0) / budget)
        if d <= 0 or rng.random() < math.exp(-d / T):
            sig, bad = sig2, bad2; acc += 1
        if bad < best[0]:
            best = (bad, sig.copy())
            print(f'it {it} t={time.time()-t0:.0f}s best {bad}', flush=True)
            save(best[1], R, out)
        if it % 200 == 0:
            print(f'it {it} t={time.time()-t0:.0f}s cur {bad} best {best[0]} acc {acc}', flush=True)
    print('done it', it, 'best', best[0], 'time', round(time.time() - t0), 'acc', acc, flush=True)
    save(best[1], R, out)
    np.savetxt(out + '.sigma', best[1], fmt='%d')
