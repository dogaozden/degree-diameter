"""orbit unions of W(E7)-subgroups on H(q) points: orbits, self-compatible orbits, exact max-weight clique."""
import sys, time, numpy as np, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r6/c5')
from grp5 import *
from mwc import max_weight_clique
def clique_exact(sizes, S, M, tlimit=60):
    n = len(S); w = [int(sizes[o]) for o in S]
    adj = [0] * n
    for i, a in enumerate(S):
        for j, b in enumerate(S):
            if i != j and M[a][j]: adj[i] |= (1 << j)
    t = time.time()
    wgt, verts, done = max_weight_clique(w, adj, tlimit)
    return wgt, [S[i] for i in verts], time.time() - t
def analyse(w, gens, name, tlimit=60):
    perms = [w.refl_perm(v) for v in gens]
    lab = orbits_from_perms(w.G.N, perms)
    members, S, M = orbit_info(w.G, lab)
    sizes = np.bincount(lab)
    print(name, 'orbits', len(sizes), 'sizes', sorted(set(sizes.tolist())), 'self-compat', len(S), 'sizes sc', sorted(sizes[S].tolist()), flush=True)
    if len(S) == 0: return None
    # quick check: is M symmetric
    wgt, cl, tt = clique_exact(sizes, S, M)
    pts = sorted(int(p) for o in cl for p in members[o])
    print(name, 'max weight clique', wgt, 'time', round(tt, 2), 'orbits', len(cl), flush=True)
    return wgt, pts, cl
if __name__ == '__main__':
    q = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    w = W(q)
    S = {}
    edges = {
     'A7': ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6)], 7),
     'D6A1': ([(0,1),(1,2),(2,3),(3,4),(3,5)], 7),
     'D6': ([(0,1),(1,2),(2,3),(3,4),(3,5)], 6),
     'E6': ([(0,1),(1,2),(2,3),(3,4),(2,5)], 6),
     'A5A2': ([(0,1),(1,2),(2,3),(3,4),(5,6)], 7),
     'D4A1^3': ([(0,1),(0,2),(0,3)], 7),
     'A3A3A1': ([(0,1),(1,2),(3,4),(4,5)], 7),
     'A1^7': ([], 7),
     'A6': ([(0,1),(1,2),(2,3),(3,4),(4,5)], 6),
     'A5': ([(0,1),(1,2),(2,3),(3,4)], 5),
     'E7': ([(0,2),(2,3),(3,4),(4,5),(5,6),(3,1)], 7),
    }
    res = {}
    for name in sys.argv[2:] if len(sys.argv) > 2 else edges.keys():
        ed, n = edges[name]
        B = w.dynkin(ed, n, seed=1, tries=200)
        if B is None:
            print(name, 'no subsystem found'); continue
        out = analyse(w, B, name)
        if out: res[name] = out
    pickle.dump(res, open('/home/user/degree-diameter/research/squads/d10D7-r6/c5/sub_q%d_res.pkl' % q, 'wb'))
