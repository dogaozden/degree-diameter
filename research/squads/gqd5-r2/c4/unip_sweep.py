"""Sweep over unipotent subgroups: cyclic order-3 transvection groups, root groups (order 9) of transvections
with common centre, and <transvection, Frobenius> style groups. Heuristic + exact max-weight union of orbits."""
import random, sys, time, json, collections
import numpy as np
import sp
from clique import max_union
from sp import F, Q, P, NP

mode = sys.argv[1]; seed = int(sys.argv[2]); N = int(sys.argv[3]); iters = int(sys.argv[4])
rng = random.Random(seed)
F3 = [0, 1, F.add[1][1]]  # placeholder
def rand_vec():
    while True:
        v = [rng.randrange(Q) for _ in range(4)]
        if any(v): return v
best = (0, None, None)
hist = collections.Counter()
t0 = time.time()
for trial in range(N):
    v = rand_vec()
    c = rng.randrange(1, Q)
    if mode == 'cyc3':
        gens = [sp.perm_of_matrix(sp.transvection(v, c))]
    elif mode == 'root9':
        # transvections with common centre v and parameters c in {1, g} with g generating F9 over F3
        c2 = rng.randrange(1, Q)
        gens = [sp.perm_of_matrix(sp.transvection(v, 1)), sp.perm_of_matrix(sp.transvection(v, c2))]
    elif mode == 'cyc3frob':
        # transvection composed with Frobenius: order divides 6
        gens = [sp.perm_of_matrix(sp.transvection(v, c))[sp.frob_perm()]]
    orbs = sp.orbits_of_group(gens)
    ordg = sp.perm_order(gens[0]) if len(gens) == 1 else 0
    w, pts, ex = max_union(orbs, iters=iters, seed=trial)
    hist[w] += 1
    if w > best[0]:
        best = (w, pts, trial)
        json.dump(best[1], open('best_%s_%d.json' % (mode, seed), 'w'))
        print(mode, 'trial', trial, 'union', w, 'exact' if ex else 'heur', 'orbit sizes', sorted(collections.Counter(len(o) for o in orbs).items()), 'time %.0f' % (time.time() - t0), flush=True)
print('done', mode, 'best', best[0], 'hist top', sorted(hist.items())[-6:], flush=True)
json.dump(best[1], open('best_%s_%d.json' % (mode, seed), 'w'))
