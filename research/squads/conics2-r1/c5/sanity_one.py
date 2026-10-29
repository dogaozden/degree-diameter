import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
from hexload import load
from transcheck import bad_pairs
q, N, LP, PL, X = load('/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q3.bin')
gam2 = []
for x in range(N):
    s = set()
    for l in PL[x]: s.update(LP[l])
    s.discard(x); gam2.append(sorted(s))
def meet(m):
    s = set()
    for p in LP[m]: s.update(PL[p])
    s.discard(m); return sorted(s)
x = 0; m0 = 5
sig = [-1] * N; sig[x] = m0
for p, l in zip(gam2[x], meet(m0)): sig[p] = l
rest_p = [p for p in range(N) if sig[p] < 0]; used = set(sig) - {-1}
rest_l = [l for l in range(N) if l not in used]
for p, l in zip(rest_p, rest_l): sig[p] = l
sig = np.array(sig, np.int64)
for R in ([x], ):
    print('R', R, 'bad_pairs', bad_pairs(q, N, LP, PL, sig, np.array(R)))
