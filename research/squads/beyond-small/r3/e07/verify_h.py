import numpy as np, sys
sys.path.insert(0,'.')
from h66 import PERMS, H
E = np.loadtxt('/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges', skiprows=1, dtype=np.int64)
keys = set((E[:,0]*33792+E[:,1]).tolist()) | set((E[:,1]*33792+E[:,0]).tolist())
def img(w, lam, t):
    side = w >= H
    loc = w - H*side
    return H*side + PERMS[(lam,t)][loc]
bad = 0
for (lam,t) in PERMS:
    u = np.where(E[:,0]<H, E[:,0], E[:,0]) # placeholder
    sA = E[:,0] < H  # edges stored with A first (u<v) since A ids < B ids
    a = E[:,0]; b = E[:,1]
    a2 = np.where(a<H, PERMS[(lam,t)][np.minimum(a,H-1)], H + PERMS[(lam,t)][np.minimum(a-H,H-1)*0 + 0*a] ) if False else None
    # vectorised image: A-side vertices stay A, B-side stay B
    A_img = PERMS[(lam,t)][a]                       # a < H
    B_img = H + PERMS[(lam,t)][b-H]                 # b >= H
    ok = all((int(x)*33792+int(y)) in keys for x,y in zip(A_img, B_img))
    if not ok: bad += 1
print('automorphisms checked', len(PERMS), 'failures', bad)
