# c8: orbits of an order-37 isometry h on E; independent orbits; orbit-compatibility clique (weight 37 each).
import sys, time
import numpy as np
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c8')
import orth as O
from ord37 import order_of, mpow

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = np.random.default_rng(seed)
    ntry = 4000
    # find a fresh order-37 element (different seeds give different subgroups in general)
    found = []
    for t in range(ntry):
        k = int(rng.integers(3, 11))
        g = O.rand_elem(rng, k)
        o = order_of(g)
        if o is not None and o % 37 == 0:
            found.append(mpow(g, o // 37))
            if len(found) >= 1: break
    h = found[0]
    t0 = time.time()
    perm = O.perm_of(h)
    cyc = O.cycles(perm)
    lens = {}
    for c in cyc: lens[len(c)] = lens.get(len(c), 0) + 1
    print("orbit sizes:", lens, flush=True)
    ind = O.indep_orbits(cyc)
    print("independent orbits:", len(ind), flush=True)
    if len(ind) >= 1:
        comp = O.compat_matrix(cyc, ind)
        n = len(ind)
        adj = []
        for a in range(n):
            bits = 0
            for b in range(n):
                if a != b and comp[a, b] and comp[b, a]:
                    bits |= 1 << b
            adj.append(bits)
        deg = [bin(x).count('1') for x in adj]
        print("compat degree: max", max(deg) if deg else 0, "mean", (sum(deg) / max(1, n)), flush=True)
        w = [len(cyc[ind[a]]) for a in range(n)]
        best, members, exact = O.max_wclique(adj, w, tlimit=60.0)
        print("max weight clique", best, "orbits", len(members), "exact", exact, flush=True)
        S = []
        for a in members: S.extend(cyc[ind[a]])
        S = sorted(S)
        print("is_indep", O.is_indep(S), "size", len(S))
        np.save(f'/home/user/degree-diameter/research/squads/d14D7-r4/c8/clique37_s{seed}.npy', np.array(S, dtype=np.int64))
        np.save(f'/home/user/degree-diameter/research/squads/d14D7-r4/c8/h37_s{seed}.npy', h)
        O.flags_of(S, f'/home/user/degree-diameter/research/squads/d14D7-r4/c8/flags_orb37_s{seed}_{best}.txt')
    print("time", round(time.time() - t0, 1))
