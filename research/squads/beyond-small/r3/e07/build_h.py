# build_h.py OUT.edges A_PKL B_PKL : G + all H-images (66 per orbit base) of hub bases; A_PKL = bases of hubs on side A (N in B)
import sys, pickle
import numpy as np
sys.path.insert(0,'/home/user/degree-diameter/research/squads/beyond-small/r3/e07')
from h66 import PERMS, H
PL = np.stack([PERMS[k] for k in sorted(PERMS)])
EDGES = '/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges'
out = sys.argv[1]
hubs = []   # (global nbr list)
for path, off in ((sys.argv[2], H), (sys.argv[3], 0)):
    bases = pickle.load(open(path, 'rb'))
    for base in bases:
        seen = set()
        for h in range(66):
            img = tuple(sorted(int(x) + off for x in PL[h, base]))
            seen.add(img)
        for img in seen: hubs.append(img)
n0 = 2 * H
use = {}
for hb in hubs:
    for w in hb: use[w] = use.get(w, 0) + 1
assert max(use.values()) == 1, 'old vertex in two hubs'
assert all(len(hb) <= 17 for hb in hubs)
with open(EDGES) as f:
    f.readline(); body = f.read()
n = n0 + len(hubs)
with open(out, 'w') as f:
    f.write(f"{n}\n"); f.write(body)
    for i, hb in enumerate(hubs):
        for w in hb: f.write(f"{n0 + i} {w}\n")
print('wrote', out, 'n', n, 'hubs', len(hubs), 'hub sizes', sorted(set(len(h) for h in hubs)))
