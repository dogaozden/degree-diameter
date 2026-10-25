# for each found cyclic group <h> (order d | 1332): orbits = cycles of h on E; independent orbits; exact max-weight
# clique of mutually non-orthogonal independent orbits. Saves the best union (point indices) to best_d<d>.npy
import sys, time, json
import numpy as np
from orth import *
Z = np.load(sys.argv[1])
tl = float(sys.argv[2]) if len(sys.argv) > 2 else 20.0
summary = {}
for key in sorted(Z.files, key=lambda s: int(s[1:])):
    d = int(key[1:]); 
    if d < 9: continue
    perm = Z[key]
    # verify order d of the permutation
    cyc = cycles(perm)
    sizes = [len(c) for c in cyc]
    from collections import Counter
    sc = Counter(sizes)
    ind = indep_orbits(cyc)
    ind_sizes = Counter(len(cyc[o]) for o in ind)
    t0 = time.time()
    comp = compat_matrix(cyc, ind)
    n = len(ind)
    if n == 0:
        print(f'd={d}: no independent orbits; orbit sizes {dict(sc)}', flush=True); continue
    adj = []
    for a in range(n):
        m = 0
        for b in range(n):
            if a != b and comp[a, b] and comp[b, a]: m |= (1 << b)
        adj.append(m)
    w = [len(cyc[o]) for o in ind]
    best, bestset, exact = max_wclique(adj, w, tlimit=tl)
    S = []
    for a in bestset: S.extend(cyc[ind[a]])
    S = np.array(sorted(S), dtype=np.int64)
    ok = is_indep(S) if len(S) else True
    print(f"d={d}: orbit size histogram {dict(sorted(sc.items()))}; independent orbits {n} sizes {dict(ind_sizes)}; "
          f"max weighted clique {best} (exact={exact}), orbits {len(bestset)}, indep check {ok}; {time.time()-t0:.1f}s", flush=True)
    summary[d] = dict(best=best, exact=exact, orbits=len(bestset))
    np.save(f"best_d{d}.npy", S)
json.dump(summary, open("analyze_summary.json", "w"), indent=1)
