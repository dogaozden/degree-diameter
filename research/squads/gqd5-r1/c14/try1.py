import random, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c14')
from surg import *
random.seed(1)
print('match edges', len(match))
# line-hub on 7 point copies taken from 7 distinct deleted matching edges
best = None
for trial in range(40):
    idx = random.sample(range(len(match)), 7)
    pts = []
    for i in idx:
        a, b = match[i]
        pts.append(a)  # a is the point copy (smaller id)
    assert all(a < 510 for a in pts)
    bcount, md, out = bad(set(idx), [pts], 'h')
    if best is None or bcount < best[0]: best = (bcount, idx)
print('best random 1-hub', best)
