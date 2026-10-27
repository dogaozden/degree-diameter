import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c3')
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from lib import *
from e7roots import e7_roots, subsystem
from run_sub_names import SUBS
q = 11
simple, R = e7_roots(q)
G = Geo(q)
S756 = np.array(sorted(int(x) for x in open('/home/user/degree-diameter/research/d10D7/sets/P11_r6c7_756.txt').read().split()))
print('756 size', len(S756), 'opp check', check_set(G, S756), flush=True)
mask = np.zeros(G.N, bool); mask[S756] = True
def closed(perms):
    return all(mask[p[S756]].all() for p in perms)
# closure under each simple reflection
sp = [G.perm(reflection_matrix(v, q)) for v in simple]
print('closed under simple reflections:', [bool(mask[p[S756]].all()) for p in sp], flush=True)
for name, (ed, n) in SUBS.items():
    t0 = time.time()
    B = subsystem(R, q, ed, n, seed=1, tries=300)
    if B is None:
        print(name, 'no subsystem', flush=True); continue
    perms = [G.perm(reflection_matrix(b, q)) for b in B]
    lab = orbit_labels(G.N, perms)
    members, counts = orbit_members(lab)
    # how many 756-points lie in orbits fully inside the set
    inside = [o for o in range(len(members)) if mask[members[o]].all()]
    cov = sum(len(members[o]) for o in inside)
    print(name, 'closed', closed(perms), 'orbits', len(members), 'orbits fully in 756:', len(inside), 'covering', cov, 'of', len(S756), flush=True)
