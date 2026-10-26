import sys, time, pickle, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
import numpy as np, slots, slots2
from grid import make_grid
P = make_grid()
NS = {9: 300, 11: 120, 13: 60}      # random-walk samples per n
SP = {9: 60, 11: 200, 13: 300}        # flip steps between samples
for n in map(int, sys.argv[1:]):
    t = time.time()
    if n <= 7:
        T = slots.all_regular_small(n)
    else:
        T = slots.circulant(n) + slots.random_regular(n, NS[n], SP[n], random.Random(n))
    best, forms_at, OUTa, INa, tida, typa, types = slots2.search(n, T, P)
    print('n', n, 'tournaments', len(T), 'candidates', len(OUTa), 'time', round(time.time()-t, 1), flush=True)
    pickle.dump(dict(P=P, n=n, best=best, forms_at=forms_at, tournaments=T, tida=tida, typa=typa, types=types),
                open('/home/user/degree-diameter/research/squads/gqd5-r1/c15/res_%d.pkl' % n, 'wb'))
