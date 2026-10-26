"""3-level test bed over Q(4,5): types D,H,H; arcs 0->1 (D->H, identity on lines, freed set = line set R),
1->2 (H->H, freed set W = the B-hub level-1 slots, bijection M12 random or annealed), 2->0 (H->D, identity on points,
freed set = ovoid O).  Hubs: for every paired line x (partner m, meeting point z):
  B-hub: slots (0,x), (1,w_x) with w_x in m\\z, (2,o) with o = O cap m (any distinct ovoid point);
  A-hub: slots (0, O cap m) [B-element of level 0], (1, x) [B-element of level 1], (2, M12(w')) for a free w'.
Unpaired freed lines get no hub (their matchings are simply deleted).  Hub graph Y by hubopt.search.
usage: pencil_build.py SETFILE OUTPREFIX [seed]
"""
import sys, json, random, os
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from setup_common import *
from levels import build, write_edges, apsp
from hubopt import hub_D0, search, bad_pairs

def main():
    setfile, out = sys.argv[1], sys.argv[2]
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    rng = random.Random(seed)
    spec = json.load(open(setfile))
    R = sorted(spec['lines']); pairs = spec['pairs']          # pairs: [l, m, z]
    oset = set(OV)
    partner = {}
    for l, m, z in pairs:
        partner[l] = (m, z); partner[m] = (l, z)
    # hub-level data
    W = []; wof = {}
    for l, m, z in pairs:
        wl = [p for p in range(N) if G.I[p, m] and p != z][0]
        wm = [p for p in range(N) if G.I[p, l] and p != z][0]
        wof[l] = wl; wof[m] = wm; W += [wl, wm]
    assert len(set(W)) == len(W)
    Ov_on = {}
    for l, m, z in pairs:
        for x, y in ((l, m), (m, l)):
            Ov_on[x] = [p for p in OV if G.I[p, y]][0]
    O_used = [Ov_on[x] for x in Ov_on]
    assert len(set(O_used)) == len(O_used)
    # M12: points -> lines; W freed.  Random bijection (or read from file if given)
    perm = list(range(N)); rng.shuffle(perm)
    if len(W) == 2 and os.environ.get('LD', '0') == '1':
        # H->H arc: two-point local duality (localdual.py) on the two B-hub points w_l, w_m
        from localdual import local_duality_pair
        lp = 0; mp = next(k for k in range(G.nl) if not G.con[lp, k] and k != lp)
        perm = local_duality_pair(G, W[0], W[1], lp, mp)
    M = {(0, 1): list(range(G.nl)), (1, 2): perm, (2, 0): list(range(N))}
    Rf = {(0, 1): set(R), (1, 2): set(W), (2, 0): set(OV)}
    arcs = [(0, 1), (1, 2), (2, 0)]
    Bhubs, Ahubs = [], []
    xs = sorted(partner)                              # paired lines
    Wl = list(W); rng.shuffle(Wl)
    Mimg = [M[(1, 2)][w] for w in Wl]
    for i, x in enumerate(xs):
        o = Ov_on[x]
        Bhubs.append([(0, x, (0, 1)), (1, wof[x], (1, 2)), (2, o, (2, 0))])
        Ahubs.append([(0, o, (2, 0)), (1, x, (0, 1)), (2, Mimg[i], (1, 2))])
    types = 'DHH'
    n, E = build(G, types, M, Rf, Bhubs, Ahubs, [], arcs=arcs)
    nv = 3 * 2 * N
    hubs = list(range(nv, nv + len(Bhubs) + len(Ahubs)))
    KB, KA = len(Bhubs), len(Ahubs)
    D0 = hub_D0(n, E, hubs)
    delta = q - 1          # hub degree 3 slots + delta <= d = q+1+r = q+2
    delta = min(delta, KA, KB)      # the hub graph is bipartite: at most min(KA,KB) neighbours per hub
    Y, cost = search(D0, KB, KA, delta, seed=seed, iters=6000)
    print('pairs', len(pairs), 'singletons', len(R) - 2 * len(pairs), 'hub cost before Y', int(cost), flush=True)
    n, E = build(G, types, M, Rf, Bhubs, Ahubs, Y, arcs=arcs)
    write_edges(out + '.edges', n, E)
    json.dump(dict(lines=R, pairs=pairs, W=W, O_used=O_used, perm=perm, Y=Y), open(out + '.json', 'w'), default=int)
    print('n', n, 'edges', len(E), flush=True)
    print(apsp(out + '.edges', 7, 5), flush=True)

if __name__ == '__main__':
    main()
