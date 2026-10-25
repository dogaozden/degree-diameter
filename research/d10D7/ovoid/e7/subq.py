"""orbit unions of reflection subgroups W(R) (R = root subsystem of E7) on H(11): exact max-weight clique."""
import sys, time, numpy as np, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/d10D7/ovoid/e7')
from orb11 import *
edges = {
 'A7': ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6)], 7),
 'D6A1': ([(0,1),(1,2),(2,3),(3,4),(3,5)], 7),
 'D6': ([(0,1),(1,2),(2,3),(3,4),(3,5)], 6),
 'E6': ([(0,1),(1,2),(2,3),(3,4),(2,5)], 6),
 'E6A1': ([(0,1),(1,2),(2,3),(3,4),(2,5)], 7),
 'A5A2': ([(0,1),(1,2),(2,3),(3,4),(5,6)], 7),
 'D4A1^3': ([(0,1),(0,2),(0,3)], 7),
 'A3A3A1': ([(0,1),(1,2),(3,4),(4,5)], 7),
 'A1^7': ([], 7),
 'A6': ([(0,1),(1,2),(2,3),(3,4),(4,5)], 6),
 'A5': ([(0,1),(1,2),(2,3),(3,4)], 5),
 'A4A2A1': ([(0,1),(1,2),(2,3),(4,5)], 7),
 'A2^3A1': ([(0,1),(2,3),(4,5)], 7),
 'A3A2A2': ([(0,1),(1,2),(3,4)], 6),
 'D5A1A1': ([(0,1),(1,2),(2,3),(3,4)], 6),
 'D4A2': ([(0,1),(0,2),(0,3),(4,5)], 6),
}
import orb11
Q = int(sys.argv[1]); orb11.CAP = Q ** 3 + 1
w = W(Q); simple, roots = load_e7(Q)
names = sys.argv[2:] if len(sys.argv) > 2 else list(edges)
res = {}
for name in names:
    ed, n = edges[name]
    t0 = time.time()
    B = w.dynkin(ed, n, seed=1, tries=300)
    if B is None: print(name, 'no subsystem', flush=True); continue
    lab = orbits_from_perms(w.G.N, [w.refl_perm(v) for v in B])
    sizes = np.bincount(lab)
    members, S, A = sc_and_compat(w.G, lab)
    if len(S) == 0:
        print(name, 'orbits', len(sizes), 'self-compat 0', flush=True); continue
    wgt, cl, done = best_union(members, S, A, tl=60)
    pts = sorted(int(p) for o in cl for p in members[o])
    print(name, 'orbits', len(sizes), 'selfcompat', len(S), 'best union', wgt, 'exact' if done else 'TIMELIMIT', 'orbit sizes', sorted(int(sizes[o]) for o in cl), '[%.0fs]' % (time.time() - t0), flush=True)
    if wgt > 0: open('/home/user/degree-diameter/research/d10D7/ovoid/e7/union_q%d_%s_%d.txt' % (Q, name.replace('^','p'), wgt), 'w').write('\n'.join(map(str, pts)) + '\n')
