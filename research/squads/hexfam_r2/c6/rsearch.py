import sys, time, random, itertools, json, numpy as np
from lib6 import *
from fam import *

def key(M): return int(''.join(str(int(x)) for x in M.reshape(-1)), 2)

def group_order(gens, cap=60000):
    I = np.eye(6, dtype=np.int64)
    seen = {key(I): I}
    frontier = [I]
    while frontier:
        nf = []
        for X in frontier:
            for g in gens:
                Y = (X @ g) % 2
                k = key(Y)
                if k not in seen:
                    seen[k] = Y; nf.append(Y)
                    if len(seen) > cap: return len(seen)
        frontier = nf
    return len(seen)

if __name__ == '__main__':
    seed = int(sys.argv[1]); trials = int(sys.argv[2]); tl = float(sys.argv[3])
    rng = random.Random(seed)
    allT = [transvection(a) for a in itertools.product([0, 1], repeat=6) if any(a)]
    best_overall = 0
    log = open('rsearch_%d.log' % seed, 'a')
    for t in range(trials):
        r = rng.choice([2, 3, 3, 4])
        gens = rng.sample(allT, r)
        go = group_order(gens, cap=20000)
        if go > 20000 or go < 6:
            continue
        perms = [perm_of(M) for M in gens]
        k, lab = orbits_of(perms)
        sizes, selfok, adj, reps = orbit_graph(lab, k)
        cand = np.nonzero(selfok)[0]
        if len(cand) == 0:
            rec = dict(t=t, r=r, order=go, k=k, selfok=0, best=0)
        else:
            w = sizes[cand].tolist()
            best, chosen = mwc_any(w, adj[np.ix_(cand, cand)], tl, seed=t)
            ids = np.nonzero(np.isin(lab, cand[chosen]))[0]
            rec = dict(t=t, r=r, order=go, k=k, selfok=len(cand), best=best)
            if best > best_overall:
                best_overall = best
                np.save('rs_best_%d.npy' % seed, ids)
                rec['gens'] = [''.join(str(int(x)) for x in M.reshape(-1)) for M in gens]
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(rec, flush=True)
    print('done best', best_overall)
