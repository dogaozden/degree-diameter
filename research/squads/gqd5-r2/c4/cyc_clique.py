import random, sys, collections, time, json
import numpy as np
import sp
from clique import max_union
rng = random.Random(int(sys.argv[1]))
N = int(sys.argv[2]); iters = int(sys.argv[3])
best_by_order = {}
t0 = time.time()
for trial in range(N):
    M = sp.random_sp(rng, 25)
    p = sp.perm_of_matrix(M)
    if rng.random() < 0.3:
        p = p[sp.frob_perm()]
    d = sp.perm_order(p)
    if d in (41, 82, 40) or d > 30 or d == 1: continue
    orbs = sp.cycles(p)
    w, pts, ex = max_union(orbs, iters=iters, seed=trial)
    if d not in best_by_order or w > best_by_order[d][0]:
        best_by_order[d] = (w, pts, trial)
        print('order', d, 'best union', w, 'exact' if ex else 'heur', 'trial', trial, 'time %.0f' % (time.time() - t0), flush=True)
best = max(best_by_order.values(), key=lambda x: x[0])
print('overall best', best[0], flush=True)
json.dump({str(k): v[0] for k, v in best_by_order.items()}, open('cyc_summary_%s.json' % sys.argv[1], 'w'))
json.dump(sorted(best[1]), open('best_cyc_%s.json' % sys.argv[1], 'w'))
