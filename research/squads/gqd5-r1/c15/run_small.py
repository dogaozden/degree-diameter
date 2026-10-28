import sys, json, time, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
import numpy as np, slots
from grid import make_grid
P = make_grid()
res = {}
for n in (3, 5, 7):
    t = time.time()
    T = slots.all_regular_small(n)
    best, tie = slots.run(n, T, P)
    res[n] = (best, tie, T)
    print('n', n, 'tourn', len(T), 'time', round(time.time()-t,1), flush=True)
pickle.dump((P, {n: (res[n][0], res[n][1]) for n in res}, {n: res[n][2] for n in res}), open('/home/user/degree-diameter/research/squads/gqd5-r1/c15/small.pkl','wb'))
for n in (3,5,7):
    best, tie, _ = res[n]
    for g in range(len(P)):
        if tuple(P[g]) in [(82,73,2),(122,111,2),(170,157,2),(100,73,2),(100,50,0)]:
            print(n, tuple(int(x) for x in P[g]), best[g], sorted(tie[g].keys())[:6], list(tie[g].values())[0])
