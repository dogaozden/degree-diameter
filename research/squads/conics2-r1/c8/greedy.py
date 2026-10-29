# randomized greedy star packing: repeatedly choose a free point p with the most entirely-free lines through it,
# take all of those lines as the pencil at p (all their points become used). Isolated lines are k=1 stars.
import sys, time
from common import *
q = int(sys.argv[1]); restarts = int(sys.argv[2]); seed = int(sys.argv[3]); noise = float(sys.argv[4]) if len(sys.argv) > 4 else 0.5
rng = np.random.default_rng(seed)
q, N, LP, PL, col, conf = setup(q)
Lc = LP.shape[0]
best = (-1, None)
t0 = time.time()
for r in range(restarts):
    used = np.zeros(N, bool)
    lineused = np.zeros(Lc, np.int64)   # number of used points on each line
    G = []; centres = []
    while True:
        free_line = (lineused == 0)
        k = free_line[PL].sum(1)               # entirely free lines through each point
        k = np.where(used, 0, k)
        m = k.max()
        if m == 0: break
        # score: prefer large k; random noise breaks ties and diversifies
        sc = k + noise * rng.random(N)
        sc = np.where(k > 0, sc, -1)
        p = int(np.argmax(sc))
        ls = [int(l) for l in PL[p] if free_line[l]]
        centres.append(p)
        for l in ls:
            G.append(l)
            for x in LP[l]:
                if not used[x]:
                    used[x] = True
                    lineused[PL[x]] += 1
    if len(G) > best[0]:
        best = (len(G), sorted(G), centres)
        print(f'restart {r}: size {len(G)} centres {len(centres)} unused points {int((~used).sum())} t={time.time()-t0:.1f}', flush=True)
print('BEST', best[0])
out = f'/home/user/degree-diameter/research/squads/conics2-r1/c8/greedy_q{q}_s{seed}.txt'
open(out, 'w').write(' '.join(map(str, best[1])) + '\n')
