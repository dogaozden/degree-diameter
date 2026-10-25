import numpy as np, sys, json, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c3')
from gen import *
K = pickle.load(open('/home/user/degree-diameter/research/squads/d14D7-r4/c3/k_samples.pkl', 'rb'))
def Tfull(o, i): return full_mat(K[o][i][2])
specs = {}
# rotation-only groups (rot^a has order 12/gcd(a,12))
specs['rot2'] = [rot_mat(6)]           # order 2
specs['rot3'] = [rot_mat(4)]           # order 3
specs['rot4'] = [rot_mat(3)]           # order 4
specs['rot6'] = [rot_mat(2)]           # order 6
# K-only cyclic groups
specs['K5a'] = [Tfull(5, 0)]
specs['K6a'] = [Tfull(6, 0)]
specs['K10a'] = [Tfull(10, 0)]
specs['K12a'] = [Tfull(12, 0)]
specs['K8a'] = [Tfull(8, 0)]
specs['K4a'] = [Tfull(4, 0)]
# rotation x K products (commuting, trivial intersection)
specs['rot6xK5a'] = [rot_mat(2), Tfull(5, 0)]          # order 30
specs['rot2xK5a'] = [rot_mat(10), Tfull(5, 0)]         # order 30? (rot^10 has order 6)
specs['rot4xK4a'] = [rot_mat(3), Tfull(4, 0)]          # order 16? check
specs['rot6xK2a'] = [rot_mat(6), Tfull(2, 0)]          # rot^6 (order 2) x K2 (order 2)
specs['rot3xK3a'] = [rot_mat(4), Tfull(3, 0)]          # order 12
specs['rot4xK6a'] = [rot_mat(3), Tfull(6, 0)]          # order 12? rot^3 order 4 x K6 order 6
specs['rot2xK2a'] = [rot_mat(2), Tfull(2, 0)]          # rot^2 (order 6) x K2
specs['rot4xK2a'] = [rot_mat(3), Tfull(2, 0)]          # order 8
specs['rot6xK10a'] = [rot_mat(6), Tfull(10, 0)]
names = sys.argv[1:] or list(specs)
out = {}
for nm in names:
    perms = [perm_of(G) for G in specs[nm]]
    roots = orbits_of(perms)
    sizes = write_perm(roots, '/home/user/degree-diameter/research/squads/d14D7-r4/c3/perms/%s.txt' % nm)
    st = stats(sizes)
    out[nm] = st
    print(nm, 'orbits', len(sizes), 'sizes', st, flush=True)
json.dump(out, open('/home/user/degree-diameter/research/squads/d14D7-r4/c3/orbit_stats.json', 'w'), indent=1)
