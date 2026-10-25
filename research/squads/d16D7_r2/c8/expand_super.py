# expand a sigma-super-row packing (list of super-row indices) into og vertex indices and write a solution file
import numpy as np, sys, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
kind, solpkl, out = sys.argv[1], sys.argv[2], sys.argv[3]
meta = pickle.load(open('hexact_meta.pkl', 'rb'))
supers = pickle.load(open(f'super_{kind}.pkl', 'rb'))
orbs = meta['orbs_l'] if kind == 'sp' else meta['orbs_p']
gof = np.load('orbit_lines.npy' if kind == 'sp' else 'orbit_pts.npy')
M, E, rep, nb = load_og(D + ('og_lines.txt' if kind == 'sp' else 'og_pts.txt'))
vid = {int(gof[rep[i]]): i for i in range(M)}
chosen = pickle.load(open(solpkl, 'rb'))
gids = set()
for si in chosen:
    orb, cols = supers[si]
    for r in orb:
        for e in orbs[r]:
            gids.add(int(gof[e]))
sol = sorted(vid[g] for g in gids)
with open(out, 'w') as f:
    f.write('\n'.join(map(str, sol)) + '\n')
print(kind, 'super-rows', len(chosen), '-> g-orbits', len(sol))
