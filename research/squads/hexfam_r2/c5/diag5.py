import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c5')
from chartlib import *
q = 5
hint_pts = eval(open('hint5_chart.txt').read())
Qp = lambda t: (t[2] * t[2] - t[0] * t[3] - t[1] * t[4]) % q
a0 = hint_pts[0]
T = [tuple((x - y) % q for x, y in zip(t, a0)) for t in hint_pts]
bad = [(u, v) for i, u in enumerate(T) for v in T[i+1:] if Qp(tuple((x-y)%q for x,y in zip(u,v))) == 0]
print('pairwise conflicts in translated hint:', len(bad))
# check Bm form equals polar of Q'
Bm = np.zeros((5,5), dtype=np.int64); Bm[2,2]=2; Bm[0,3]=Bm[3,0]=-1; Bm[1,4]=Bm[4,1]=-1
rng = np.random.default_rng(0)
ok = True
for _ in range(200):
    x, y = rng.integers(0,q,5), rng.integers(0,q,5)
    Qx = lambda t: (t[2]*t[2]-t[0]*t[3]-t[1]*t[4])
    polar = Qx(x+y) - Qx(x) - Qx(y)
    if int(x @ Bm @ y) % q != polar % q: ok = False
print('Bm matches polar form of Q\':', ok)
