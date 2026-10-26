"""Build a typed5 state with local-duality matchings on the non-friendly arcs (as build_typed LD=1), R = 2 points/lines."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import typed5 as T
from localdual import local_duality_pair, pick_pair
from gqlib import W
Wq = W(T.Q)
def ld_state(c=2, cp=2, seed=0):
    s = T.State(); rng = np.random.default_rng(seed)
    for t in T.ARCS:
        f = T.friendly_R(t)
        if f is not None:
            s.R[t] = f; s.M[t] = np.arange(T.N); continue
        if T.TYPES[t[0]] == 'H':
            x, y, l, m = pick_pair(T.G, avoid_pts=T.OVOID)
            s.M[t] = np.array(local_duality_pair(T.G, x, y, l, m)); s.R[t] = sorted({x, y})
        else:
            x, y, l, m = pick_pair(Wq, avoid_pts=T.PSPREAD)
            s.M[t] = np.array(local_duality_pair(Wq, x, y, l, m)); s.R[t] = sorted({x, y})
    T.set_hubs(s, rng)
    return s
if __name__ == '__main__':
    s = ld_state()
    print('KB', s.KB, 'KA', s.KA, 'bad', T.bad_count(s))
