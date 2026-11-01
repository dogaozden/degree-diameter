# Rule test: lifts of label multisets ranked by max_t |phi_t|/Delta (Fourier balance of the Z_19 labels).
import sys, itertools, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/r2/h17')
from frob import Frob, covers
p, k, r, h, D = 761, 19, 25, 5, 11
G = Frob(p, k, r); N = G.N; d = 4
w = np.exp(2j * np.pi / k)
def maxphi(labels):
    return max(abs(sum(w ** (t * c) for c in labels)) for t in range(1, k)) / d
sets = []
for rest in itertools.combinations(range(1, k), d - 1):
    labels = (0,) + rest
    if len(set(labels)) == d:
        sets.append((maxphi(labels), labels))
sets.sort()
groups = {'best 10 sets': sets[:10], 'middle 10 sets': sets[len(sets)//2 - 5: len(sets)//2 + 5], 'worst 10 sets': sets[-10:]}
rng = np.random.default_rng(3)
t0 = time.time()
for name, grp in groups.items():
    tot = 0; exact = 0; hol = []
    for mp, labels in grp:
        for _ in range(7):
            # lift each non-e label to a random element of that coset (a uniform in Z_p, a!=0 not needed)
            S = [0] + [int(rng.integers(0, p)) * k + c for c in labels[1:]]
            if len(set(S)) < d: continue
            XA, XB = covers(G, S, D)
            hA = int((~XA).sum()); hB = int((~XB).sum())
            tot += 1; exact += (hA == 0 and hB == 0); hol.append(hA)
    print(name, 'maxphi %.3f-%.3f' % (grp[0][0], grp[-1][0]), 'trials', tot, 'exact cover (both sides)', exact,
          'median holes A', int(np.median(hol)), 'time', round(time.time() - t0, 1))
    if time.time() - t0 > 80: break
