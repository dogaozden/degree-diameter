import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r6/c5')
from grp5 import *
w = W(5)
print('roots', len(w.roots), 'N', w.G.N)
# simple reflections as perms, check they are involutions and isometries on points
t = time.time()
ps = [w.refl_perm(v) for v in w.simple]
print('perm build', time.time() - t)
print('involution:', all((p[p] == np.arange(len(p))).all() for p in ps))
lab = orbits_from_perms(w.G.N, ps)
print('W(E7) orbits on points: sizes', np.bincount(lab).tolist())
systems = {
 'A7': [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6)],
 'D6': [(0,1),(1,2),(2,3),(3,4),(3,5)],
 'E6': [(0,1),(1,2),(2,3),(3,4),(2,5)],
 'A5A2': [(0,1),(1,2),(2,3),(3,4),(5,6)],
 'D4A1^3': [(0,1),(0,2),(0,3)],
 'A3A3A1': [(0,1),(1,2),(3,4),(4,5)],
 'A1^7': [],
 'D6A1': [(0,1),(1,2),(2,3),(3,4),(3,5)],
}
nodes = {'A7':7,'D6':6,'E6':6,'A5A2':7,'D4A1^3':7,'A3A3A1':7,'A1^7':7,'D6A1':7}
for name, ed in systems.items():
    n = nodes[name]
    if name == 'D4A1^3': ed = [(0,1),(0,2),(0,3)]
    if name == 'D6A1': ed = [(0,1),(1,2),(2,3),(3,4),(3,5)]  # 6 nodes + extra orthogonal node added below
    if name == 'A3A3A1': ed = [(0,1),(1,2),(3,4),(4,5)]
    t = time.time()
    B = w.dynkin(ed, n, seed=1, tries=200)
    print(name, 'found' if B is not None else 'NOT found', round(time.time() - t, 2), 's')
