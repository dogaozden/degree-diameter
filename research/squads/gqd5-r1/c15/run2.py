import sys, time, pickle, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
import numpy as np, slots, slots2
from grid import make_grid
P = make_grid()
CAP = {7: None, 9: None, 11: 150, 13: 60}
SAMP = {7: 0, 9: 6000, 11: 8000, 13: 6000}
for n in map(int, sys.argv[1:]):
    t = time.time()
    if n == 7:
        pool = slots.all_regular_small(7)
    else:
        rng = random.Random(n)
        pool = slots.circulant(n) + slots.random_regular(n, SAMP[n], 20 if n == 9 else 40, rng)
    T = slots.dedupe(pool, CAP[n])
    print('n', n, 'classes(reps)', len(T), 'time', round(time.time()-t, 1), flush=True)
    best, forms_at, OUTa, INa, tida, typa, types = slots2.search(n, T, P)
    print('n', n, 'candidates', len(OUTa), 'search time', round(time.time()-t, 1), flush=True)
    pickle.dump(dict(P=P, n=n, best=best, forms_at=forms_at, tournaments=T, tida=tida, typa=typa, types=types),
                open('/home/user/degree-diameter/research/squads/gqd5-r1/c15/res_%d.pkl' % n, 'wb'))
