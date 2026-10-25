# expand a quotient solution (indices into quot2 rows) to og vertex indices and write a solution file
import numpy as np, sys, pickle, subprocess
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
kind, qsol, out = sys.argv[1], sys.argv[2], sys.argv[3]
meta = pickle.load(open('hexact_meta.pkl', 'rb'))
mp = pickle.load(open(f'quot2_{kind}_map.pkl', 'rb'))
orbs = meta['orbs_l'] if kind == 'sp' else meta['orbs_p']
gof = np.load('orbit_lines.npy' if kind == 'sp' else 'orbit_pts.npy')
M, E, rep, nb = load_og(D + ('og_lines.txt' if kind == 'sp' else 'og_pts.txt'))
vid = {int(gof[rep[i]]): i for i in range(M)}
idx = [int(x) for x in open(qsol).read().split() if x.strip()]
gids = set()
for i in idx:
    rid = mp['rid'][i]
    for e in orbs[rid]:
        gids.add(int(gof[e]))
sol = sorted(vid[g] for g in gids)
with open(out, 'w') as f:
    f.write('\n'.join(map(str, sol)) + '\n')
print('quotient rows', len(idx), '-> g-orbits', len(sol))
